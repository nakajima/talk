"use strict";
/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
exports.deactivate = deactivate;
const fs_1 = require("fs");
const os_1 = require("os");
const path_1 = require("path");
const vscode_1 = require("vscode");
const node_1 = require("vscode-languageclient/node");
const testing_1 = require("./testing");
let client;
let restartPromise;
function expandHome(path) {
    if (path === "~") {
        return (0, os_1.homedir)();
    }
    if (path.startsWith("~/")) {
        return (0, os_1.homedir)() + path.slice(1);
    }
    return path;
}
function configuredBinaryPath() {
    const binaryPath = vscode_1.workspace
        .getConfiguration("talktalk")
        .get("binaryPath")
        ?.trim();
    return binaryPath
        ? expandHome(binaryPath)
        : (0, os_1.homedir)() + "/apps/talk/target/debug/talk";
}
function configuredCorePath() {
    const corePath = vscode_1.workspace
        .getConfiguration("talktalk")
        .get("corePath")
        ?.trim();
    if (corePath) {
        return expandHome(corePath);
    }
    const envCorePath = process.env.TALK_CORE_PATH?.trim();
    if (envCorePath) {
        return expandHome(envCorePath);
    }
    return undefined;
}
function configuredStdlibPath() {
    const stdlibPath = vscode_1.workspace
        .getConfiguration("talktalk")
        .get("stdlibPath")
        ?.trim();
    if (stdlibPath) {
        return expandHome(stdlibPath);
    }
    const envStdlibPath = process.env.TALK_STDLIB_PATH?.trim();
    if (envStdlibPath) {
        return expandHome(envStdlibPath);
    }
    return undefined;
}
function repositoryRootFrom(startPath) {
    let current = startPath;
    while (true) {
        if ((0, fs_1.existsSync)((0, path_1.join)(current, "scripts/reinstall-vscode-extension.sh")) &&
            (0, fs_1.existsSync)((0, path_1.join)(current, "dev/editors/vscode/package.json"))) {
            return current;
        }
        const parent = (0, path_1.dirname)(current);
        if (parent === current) {
            return undefined;
        }
        current = parent;
    }
}
function configuredRepositoryRoot() {
    const candidates = [
        ...(vscode_1.workspace.workspaceFolders ?? [])
            .filter((folder) => folder.uri.scheme === "file")
            .map((folder) => folder.uri.fsPath),
        configuredBinaryPath(),
        process.cwd(),
        (0, path_1.join)((0, os_1.homedir)(), "apps/talk"),
    ];
    for (const candidate of candidates) {
        const root = repositoryRootFrom(candidate);
        if (root) {
            return root;
        }
    }
    return undefined;
}
function reinstallExtension() {
    const repositoryRoot = configuredRepositoryRoot();
    if (!repositoryRoot) {
        vscode_1.window.showErrorMessage("Could not locate the Talk repository. Open the repository or set talktalk.binaryPath to its target/debug/talk binary.");
        return;
    }
    const terminal = vscode_1.window.createTerminal({
        name: "TalkTalk Reinstall",
        cwd: repositoryRoot,
        shellPath: (0, path_1.join)(repositoryRoot, "scripts/reinstall-vscode-extension.sh"),
    });
    terminal.show();
}
function configuredEnvironment() {
    const corePath = configuredCorePath();
    const stdlibPath = configuredStdlibPath();
    return {
        ...process.env,
        ...(corePath ? { TALK_CORE_PATH: corePath } : {}),
        ...(stdlibPath ? { TALK_STDLIB_PATH: stdlibPath } : {}),
    };
}
function serverOptions() {
    return {
        command: configuredBinaryPath(),
        transport: node_1.TransportKind.stdio,
        args: ["lsp"],
        options: {
            env: {
                ...configuredEnvironment(),
                RUST_LOG: process.env.RUST_LOG ?? "debug",
            },
        },
    };
}
async function restartLanguageServer() {
    if (client) {
        await client.stop();
    }
    client = createClient();
    await client.start();
}
let createClient;
async function setCorePath() {
    const current = configuredCorePath();
    const devCorePath = (0, os_1.homedir)() + "/apps/talk/core";
    const defaultPath = current ?? ((0, fs_1.existsSync)(devCorePath) ? devCorePath : (0, os_1.homedir)());
    const selected = await vscode_1.window.showOpenDialog({
        canSelectFiles: false,
        canSelectFolders: true,
        canSelectMany: false,
        defaultUri: vscode_1.Uri.file(defaultPath),
        openLabel: "Use as TALK_CORE_PATH",
        title: "Select Talk core directory",
    });
    const folder = selected?.[0]?.fsPath;
    if (!folder) {
        return;
    }
    const target = vscode_1.workspace.workspaceFolders?.length
        ? vscode_1.ConfigurationTarget.Workspace
        : vscode_1.ConfigurationTarget.Global;
    await vscode_1.workspace.getConfiguration("talktalk").update("corePath", folder, target);
    const restart = await vscode_1.window.showInformationMessage(`TalkTalk core path set to ${folder}.`, "Restart Language Server");
    if (restart === "Restart Language Server") {
        await vscode_1.commands.executeCommand("talktalk.restartLsp");
    }
}
async function clearCorePath() {
    const target = vscode_1.workspace.workspaceFolders?.length
        ? vscode_1.ConfigurationTarget.Workspace
        : vscode_1.ConfigurationTarget.Global;
    await vscode_1.workspace.getConfiguration("talktalk").update("corePath", undefined, target);
    const restart = await vscode_1.window.showInformationMessage("TalkTalk core path cleared.", "Restart Language Server");
    if (restart === "Restart Language Server") {
        await vscode_1.commands.executeCommand("talktalk.restartLsp");
    }
}
async function setStdlibPath() {
    const current = configuredStdlibPath();
    const devStdlibPath = (0, os_1.homedir)() + "/apps/talk/stdlib";
    const defaultPath = current ?? ((0, fs_1.existsSync)(devStdlibPath) ? devStdlibPath : (0, os_1.homedir)());
    const selected = await vscode_1.window.showOpenDialog({
        canSelectFiles: false,
        canSelectFolders: true,
        canSelectMany: false,
        defaultUri: vscode_1.Uri.file(defaultPath),
        openLabel: "Use as TALK_STDLIB_PATH",
        title: "Select Talk stdlib directory",
    });
    const folder = selected?.[0]?.fsPath;
    if (!folder) {
        return;
    }
    const target = vscode_1.workspace.workspaceFolders?.length
        ? vscode_1.ConfigurationTarget.Workspace
        : vscode_1.ConfigurationTarget.Global;
    await vscode_1.workspace.getConfiguration("talktalk").update("stdlibPath", folder, target);
    const restart = await vscode_1.window.showInformationMessage(`TalkTalk stdlib path set to ${folder}.`, "Restart Language Server");
    if (restart === "Restart Language Server") {
        await vscode_1.commands.executeCommand("talktalk.restartLsp");
    }
}
async function clearStdlibPath() {
    const target = vscode_1.workspace.workspaceFolders?.length
        ? vscode_1.ConfigurationTarget.Workspace
        : vscode_1.ConfigurationTarget.Global;
    await vscode_1.workspace.getConfiguration("talktalk").update("stdlibPath", undefined, target);
    const restart = await vscode_1.window.showInformationMessage("TalkTalk stdlib path cleared.", "Restart Language Server");
    if (restart === "Restart Language Server") {
        await vscode_1.commands.executeCommand("talktalk.restartLsp");
    }
}
function activate(context) {
    // Options to control the language client
    const clientOptions = {
        // Register the server for plain text documents
        documentSelector: [{ scheme: "file", language: "talktalk" }],
        synchronize: {
            // Notify the server about file changes to '.clientrc files contained in the workspace
            fileEvents: vscode_1.workspace.createFileSystemWatcher("**/*.tlk"),
        },
    };
    createClient = () => new node_1.LanguageClient("TalkTalk", "TalkTalk Language Server", serverOptions(), clientOptions);
    (0, testing_1.registerTalkTestController)(context, {
        binaryPath: configuredBinaryPath,
        environment: configuredEnvironment,
    });
    context.subscriptions.push(vscode_1.commands.registerCommand("talktalk.restartLsp", async () => {
        restartPromise ??= restartLanguageServer()
            .then(() => {
            vscode_1.window.showInformationMessage("TalkTalk language server restarted.");
        })
            .finally(() => {
            restartPromise = undefined;
        });
        return restartPromise;
    }), vscode_1.commands.registerCommand("talktalk.reinstallExtension", reinstallExtension), vscode_1.commands.registerCommand("talktalk.setCorePath", setCorePath), vscode_1.commands.registerCommand("talktalk.clearCorePath", clearCorePath), vscode_1.commands.registerCommand("talktalk.setStdlibPath", setStdlibPath), vscode_1.commands.registerCommand("talktalk.clearStdlibPath", clearStdlibPath));
    // Create the language client and start the client.
    client = createClient();
    // Start the client. This will also launch the server
    client.start();
}
function deactivate() {
    if (!client) {
        return undefined;
    }
    return client.stop();
}
//# sourceMappingURL=extension.js.map