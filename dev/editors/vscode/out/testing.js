"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.discoverTalkTests = discoverTalkTests;
exports.registerTalkTestController = registerTalkTestController;
const child_process_1 = require("child_process");
const path_1 = require("path");
const vscode_1 = require("vscode");
const ignoredDirectoryNames = new Set([".claude", ".git", "node_modules", "target"]);
const testFilePattern = "**/*.test.tlk";
const testFileExcludePattern = "**/{.claude,.git,node_modules,target}/**";
function isWordCharacter(character) {
    return /^[A-Za-z0-9_]$/.test(character);
}
function readTestName(line) {
    if (/^\s*\/\//.test(line)) {
        return undefined;
    }
    const declaration = /^\s*test/.exec(line);
    if (!declaration) {
        return undefined;
    }
    let index = declaration[0].length;
    const nextCharacter = line[index] ?? "";
    if (nextCharacter && isWordCharacter(nextCharacter)) {
        return undefined;
    }
    while (/\s/.test(line[index] ?? "")) {
        index += 1;
    }
    if (line[index] === "(") {
        index += 1;
        while (/\s/.test(line[index] ?? "")) {
            index += 1;
        }
    }
    if (line[index] !== '"') {
        return undefined;
    }
    index += 1;
    let name = "";
    while (index < line.length) {
        const character = line[index];
        if (character === '"') {
            return name;
        }
        if (character !== "\\") {
            name += character;
            index += 1;
            continue;
        }
        const escaped = line[index + 1];
        if (escaped === undefined) {
            return undefined;
        }
        switch (escaped) {
            case "n":
                name += "\n";
                index += 2;
                break;
            case "r":
                name += "\r";
                index += 2;
                break;
            case "t":
                name += "\t";
                index += 2;
                break;
            case '"':
                name += '"';
                index += 2;
                break;
            case "\\":
                name += "\\";
                index += 2;
                break;
            case "u": {
                if (line[index + 2] !== "{") {
                    name += escaped;
                    index += 2;
                    break;
                }
                const close = line.indexOf("}", index + 3);
                if (close === -1) {
                    name += escaped;
                    index += 2;
                    break;
                }
                const codePoint = Number.parseInt(line.slice(index + 3, close), 16);
                if (Number.isFinite(codePoint) &&
                    codePoint >= 0 &&
                    codePoint <= 0x10ffff &&
                    !(codePoint >= 0xd800 && codePoint <= 0xdfff)) {
                    name += String.fromCodePoint(codePoint);
                }
                index = close + 1;
                break;
            }
            default:
                name += escaped;
                index += 2;
                break;
        }
    }
    return undefined;
}
function findTestEnd(lines, startLine) {
    let depth = 0;
    let sawOpeningBrace = false;
    let inString = false;
    let escaped = false;
    for (let lineIndex = startLine; lineIndex < lines.length; lineIndex += 1) {
        const line = lines[lineIndex];
        for (let characterIndex = 0; characterIndex < line.length; characterIndex += 1) {
            const character = line[characterIndex];
            const nextCharacter = line[characterIndex + 1];
            if (inString) {
                if (escaped) {
                    escaped = false;
                }
                else if (character === "\\") {
                    escaped = true;
                }
                else if (character === '"') {
                    inString = false;
                }
            }
            else if (character === "/" && nextCharacter === "/") {
                break;
            }
            else if (character === '"') {
                inString = true;
            }
            else if (character === "{") {
                depth += 1;
                sawOpeningBrace = true;
            }
            else if (character === "}") {
                depth -= 1;
                if (sawOpeningBrace && depth <= 0) {
                    return { line: lineIndex, character: line.length };
                }
            }
        }
    }
    return { line: startLine, character: lines[startLine]?.length ?? 0 };
}
function discoverTalkTests(source) {
    const lines = source.split(/\r?\n/);
    const discovered = [];
    for (let lineIndex = 0; lineIndex < lines.length; lineIndex += 1) {
        const name = readTestName(lines[lineIndex]);
        if (name === undefined) {
            continue;
        }
        const end = findTestEnd(lines, lineIndex);
        discovered.push({
            name,
            range: new vscode_1.Range(lineIndex, 0, end.line, end.character),
        });
    }
    return discovered;
}
function isTestFile(uri) {
    return uri.scheme === "file" && uri.path.endsWith(".test.tlk");
}
function isIgnored(uri) {
    return uri.path.split("/").some((part) => ignoredDirectoryNames.has(part));
}
function reportFromJson(output) {
    let parsed;
    try {
        parsed = JSON.parse(output.trim());
    }
    catch {
        return undefined;
    }
    if (!parsed || typeof parsed !== "object") {
        return undefined;
    }
    const value = parsed;
    if (typeof value.status !== "string" ||
        typeof value.failures !== "number" ||
        !Array.isArray(value.tests) ||
        typeof value.output !== "string") {
        return undefined;
    }
    if (value.status === "no_tests") {
        return value.tests.length === 0 ? parsed : undefined;
    }
    if (value.status === "error") {
        const error = value.error;
        if (value.tests.length !== 0 ||
            !error ||
            typeof error !== "object" ||
            typeof error.message !== "string") {
            return undefined;
        }
        return parsed;
    }
    if (value.status !== "finished") {
        return undefined;
    }
    for (const test of value.tests) {
        if (!test || typeof test !== "object") {
            return undefined;
        }
        const result = test;
        if (typeof result.name !== "string" ||
            (result.status !== "passed" && result.status !== "failed") ||
            !Array.isArray(result.failures) ||
            !result.failures.every((failure) => typeof failure === "string")) {
            return undefined;
        }
    }
    return parsed;
}
function outputForTestRun(output) {
    const normalized = output.replace(/\r?\n/g, "\r\n");
    return normalized.endsWith("\r\n") ? normalized : `${normalized}\r\n`;
}
function mergeInvocationStatus(current, next) {
    const priority = {
        skipped: 0,
        passed: 1,
        cancelled: 2,
        failed: 3,
        errored: 4,
    };
    return priority[next] > priority[current] ? next : current;
}
function testMessage(message, item) {
    const result = new vscode_1.TestMessage(message);
    if (item.uri && item.range) {
        result.location = new vscode_1.Location(item.uri, item.range);
    }
    return result;
}
function runProcess(command, args, cwd, environment, token) {
    return new Promise((resolve) => {
        const child = (0, child_process_1.spawn)(command, args, {
            cwd,
            env: environment,
            windowsHide: true,
        });
        let stdout = "";
        let stderr = "";
        let spawnError;
        child.stdout.setEncoding("utf8");
        child.stderr.setEncoding("utf8");
        child.stdout.on("data", (chunk) => {
            stdout += chunk;
        });
        child.stderr.on("data", (chunk) => {
            stderr += chunk;
        });
        child.on("error", (error) => {
            spawnError = error;
        });
        const cancellation = token.onCancellationRequested(() => {
            child.kill();
        });
        child.on("close", () => {
            cancellation.dispose();
            resolve({
                stdout,
                stderr,
                error: spawnError,
                cancelled: token.isCancellationRequested,
            });
        });
    });
}
function collectionItems(item) {
    const items = [];
    item.children.forEach((child) => items.push(child));
    return items;
}
function appendReportOutput(run, report, stderr, item) {
    if (report.output) {
        run.appendOutput(outputForTestRun(report.output), undefined, item);
    }
    if (stderr) {
        run.appendOutput(outputForTestRun(stderr), undefined, item);
    }
}
function registerTalkTestController(context, configuration) {
    const controller = vscode_1.tests.createTestController("talktalkTests", "TalkTalk");
    const metadata = new WeakMap();
    const updateFileFromSource = (uri, source) => {
        if (!isTestFile(uri) || isIgnored(uri)) {
            return;
        }
        const id = uri.toString();
        let file = controller.items.get(id);
        if (!file) {
            file = controller.createTestItem(id, vscode_1.workspace.asRelativePath(uri, false), uri);
            controller.items.add(file);
        }
        file.label = vscode_1.workspace.asRelativePath(uri, false);
        metadata.set(file, { kind: "file", uri });
        const occurrences = new Map();
        const children = discoverTalkTests(source).map((discovered) => {
            const occurrence = occurrences.get(discovered.name) ?? 0;
            occurrences.set(discovered.name, occurrence + 1);
            const testId = `${id}::${encodeURIComponent(discovered.name)}::${occurrence}`;
            const existing = file?.children.get(testId);
            const test = existing ?? controller.createTestItem(testId, discovered.name, uri);
            test.label = discovered.name;
            test.range = discovered.range;
            metadata.set(test, {
                kind: "test",
                uri,
                name: discovered.name,
                occurrence,
            });
            return test;
        });
        file.children.replace(children);
        controller.invalidateTestResults(file);
    };
    const updateFile = async (uri) => {
        const openDocument = vscode_1.workspace.textDocuments.find((document) => document.uri.toString() === uri.toString());
        if (openDocument) {
            updateFileFromSource(uri, openDocument.getText());
            return;
        }
        try {
            const contents = await vscode_1.workspace.fs.readFile(uri);
            updateFileFromSource(uri, Buffer.from(contents).toString("utf8"));
        }
        catch {
            controller.items.delete(uri.toString());
        }
    };
    const refresh = async (token) => {
        const files = await vscode_1.workspace.findFiles(testFilePattern, testFileExcludePattern);
        if (token?.isCancellationRequested) {
            return;
        }
        const found = new Set(files.map((uri) => uri.toString()));
        const removed = [];
        controller.items.forEach((item) => {
            if (!found.has(item.id)) {
                removed.push(item.id);
            }
        });
        for (const id of removed) {
            controller.items.delete(id);
        }
        await Promise.all(files.map(updateFile));
    };
    const buildRunPlans = (request) => {
        const excluded = new Set(request.exclude ?? []);
        const plans = new Map();
        const addTest = (test) => {
            if (excluded.has(test)) {
                return;
            }
            const testData = metadata.get(test);
            if (!testData || testData.kind !== "test") {
                return;
            }
            const file = controller.items.get(testData.uri.toString());
            if (!file || excluded.has(file)) {
                return;
            }
            const plan = plans.get(file.id) ?? { file, tests: [], includeFile: false };
            if (!plan.tests.includes(test)) {
                plan.tests.push(test);
            }
            plans.set(file.id, plan);
        };
        const addFile = (file) => {
            if (excluded.has(file)) {
                return;
            }
            const fileData = metadata.get(file);
            if (!fileData || fileData.kind !== "file") {
                return;
            }
            const plan = plans.get(file.id) ?? { file, tests: [], includeFile: true };
            plan.includeFile = true;
            for (const child of collectionItems(file)) {
                if (!excluded.has(child) && !plan.tests.includes(child)) {
                    plan.tests.push(child);
                }
            }
            plans.set(file.id, plan);
        };
        if (request.include) {
            for (const item of request.include) {
                const itemData = metadata.get(item);
                if (itemData?.kind === "file") {
                    addFile(item);
                }
                else {
                    addTest(item);
                }
            }
        }
        else {
            controller.items.forEach(addFile);
        }
        return [...plans.values()];
    };
    const executeInvocation = async (run, file, selectedTests, filter, token) => {
        const fileData = metadata.get(file);
        if (!fileData || fileData.kind !== "file") {
            return "errored";
        }
        for (const item of selectedTests) {
            run.started(item);
        }
        const folder = vscode_1.workspace.getWorkspaceFolder(fileData.uri);
        const cwd = folder?.uri.fsPath ?? (0, path_1.dirname)(fileData.uri.fsPath);
        const args = ["test", "--json"];
        if (filter !== undefined) {
            args.push("--filter", filter);
        }
        args.push(fileData.uri.fsPath);
        const processResult = await runProcess(configuration.binaryPath(), args, cwd, configuration.environment(), token);
        if (processResult.cancelled) {
            for (const item of selectedTests) {
                run.skipped(item);
            }
            return "cancelled";
        }
        if (processResult.error) {
            const message = processResult.error.message;
            for (const item of selectedTests) {
                run.errored(item, testMessage(message, item));
            }
            return "errored";
        }
        const report = reportFromJson(processResult.stdout);
        if (!report) {
            const detail = processResult.stderr.trim() || processResult.stdout.trim();
            const message = detail
                ? `talk test --json did not produce valid JSON\n${detail}`
                : "talk test --json did not produce valid JSON";
            for (const item of selectedTests) {
                run.errored(item, testMessage(message, item));
            }
            return "errored";
        }
        appendReportOutput(run, report, processResult.stderr, selectedTests[0] ?? file);
        if (report.status === "error") {
            for (const item of selectedTests) {
                run.errored(item, testMessage(report.error.message, item));
            }
            return "errored";
        }
        if (report.status === "no_tests") {
            for (const item of selectedTests) {
                run.skipped(item);
            }
            return "skipped";
        }
        const resultsByName = new Map();
        for (const result of report.tests) {
            const matching = resultsByName.get(result.name) ?? [];
            matching.push(result);
            resultsByName.set(result.name, matching);
        }
        let failed = report.failures > 0;
        for (const item of selectedTests) {
            const itemData = metadata.get(item);
            if (!itemData || itemData.kind !== "test") {
                run.errored(item, testMessage("TalkTalk test metadata is unavailable", item));
                failed = true;
                continue;
            }
            const matching = resultsByName.get(itemData.name) ?? [];
            const result = matching[itemData.occurrence];
            if (!result) {
                run.errored(item, testMessage(`talk test did not report a result for '${itemData.name}'`, item));
                failed = true;
            }
            else if (result.status === "failed") {
                const failures = result.failures.length > 0 ? result.failures : ["test failed"];
                run.failed(item, failures.map((failure) => testMessage(failure, item)));
                failed = true;
            }
            else {
                run.passed(item);
            }
        }
        return failed ? "failed" : "passed";
    };
    const runHandler = async (request, token) => {
        const run = controller.createTestRun(request);
        const plans = buildRunPlans(request);
        const unfinished = new Set();
        for (const plan of plans) {
            for (const item of plan.tests) {
                run.enqueued(item);
                unfinished.add(item);
            }
        }
        try {
            for (const plan of plans) {
                if (token.isCancellationRequested) {
                    break;
                }
                const fileData = metadata.get(plan.file);
                if (!fileData || fileData.kind !== "file") {
                    continue;
                }
                const document = vscode_1.workspace.textDocuments.find((candidate) => candidate.uri.toString() === fileData.uri.toString());
                if (document?.isDirty && !(await document.save())) {
                    for (const item of plan.tests) {
                        run.errored(item, testMessage(`Could not save ${fileData.uri.fsPath}`, item));
                        unfinished.delete(item);
                    }
                    if (plan.includeFile) {
                        run.errored(plan.file, new vscode_1.TestMessage(`Could not save ${fileData.uri.fsPath}`));
                    }
                    continue;
                }
                if (plan.tests.length === 0) {
                    if (plan.includeFile) {
                        run.started(plan.file);
                        const result = await executeInvocation(run, plan.file, [], undefined, token);
                        if (result === "errored") {
                            run.errored(plan.file, new vscode_1.TestMessage("talk test failed"));
                        }
                        else {
                            run.skipped(plan.file);
                        }
                    }
                    continue;
                }
                if (plan.includeFile) {
                    run.started(plan.file);
                }
                let fileResult = "skipped";
                const allTests = collectionItems(plan.file);
                const runsWholeFile = plan.tests.length === allTests.length && allTests.every((item) => plan.tests.includes(item));
                if (runsWholeFile) {
                    fileResult = await executeInvocation(run, plan.file, plan.tests, undefined, token);
                    for (const item of plan.tests) {
                        unfinished.delete(item);
                    }
                }
                else {
                    const testsByName = new Map();
                    for (const item of plan.tests) {
                        const itemData = metadata.get(item);
                        if (!itemData || itemData.kind !== "test") {
                            continue;
                        }
                        const matching = testsByName.get(itemData.name) ?? [];
                        matching.push(item);
                        testsByName.set(itemData.name, matching);
                    }
                    for (const [name, matching] of testsByName) {
                        if (token.isCancellationRequested) {
                            fileResult = "cancelled";
                            break;
                        }
                        const result = await executeInvocation(run, plan.file, matching, name, token);
                        for (const item of matching) {
                            unfinished.delete(item);
                        }
                        fileResult = mergeInvocationStatus(fileResult, result);
                    }
                }
                if (plan.includeFile) {
                    if (fileResult === "passed") {
                        run.passed(plan.file);
                    }
                    else if (fileResult === "failed") {
                        run.failed(plan.file, new vscode_1.TestMessage("One or more tests failed"));
                    }
                    else if (fileResult === "errored") {
                        run.errored(plan.file, new vscode_1.TestMessage("talk test failed"));
                    }
                    else {
                        run.skipped(plan.file);
                    }
                }
            }
        }
        finally {
            for (const item of unfinished) {
                run.skipped(item);
            }
            run.end();
        }
    };
    controller.createRunProfile("Run", vscode_1.TestRunProfileKind.Run, runHandler, true);
    controller.resolveHandler = async (item) => {
        if (item?.uri) {
            await updateFile(item.uri);
        }
        else {
            await refresh();
        }
    };
    controller.refreshHandler = refresh;
    const watcher = vscode_1.workspace.createFileSystemWatcher(testFilePattern);
    context.subscriptions.push(controller, watcher, watcher.onDidCreate((uri) => {
        if (!isIgnored(uri)) {
            void updateFile(uri);
        }
    }), watcher.onDidChange((uri) => {
        if (!isIgnored(uri)) {
            void updateFile(uri);
        }
    }), watcher.onDidDelete((uri) => controller.items.delete(uri.toString())), vscode_1.workspace.onDidOpenTextDocument((document) => {
        if (isTestFile(document.uri) && !isIgnored(document.uri)) {
            updateFileFromSource(document.uri, document.getText());
        }
    }), vscode_1.workspace.onDidChangeTextDocument((event) => {
        if (isTestFile(event.document.uri) && !isIgnored(event.document.uri)) {
            updateFileFromSource(event.document.uri, event.document.getText());
        }
    }));
    for (const document of vscode_1.workspace.textDocuments) {
        if (isTestFile(document.uri) && !isIgnored(document.uri)) {
            updateFileFromSource(document.uri, document.getText());
        }
    }
    void refresh();
    return controller;
}
//# sourceMappingURL=testing.js.map