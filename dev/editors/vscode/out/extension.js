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
const vscode_1 = require("vscode");
const node_1 = require("vscode-languageclient/node");
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
function serverOptions() {
    const corePath = configuredCorePath();
    const env = {
        ...process.env,
        RUST_LOG: process.env.RUST_LOG ?? "debug",
        ...(corePath ? { TALK_CORE_PATH: corePath } : {}),
    };
    return {
        command: (0, os_1.homedir)() + "/apps/talk/target/debug/talk",
        transport: node_1.TransportKind.stdio,
        args: ["lsp"],
        options: { env },
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
    context.subscriptions.push(vscode_1.commands.registerCommand("talktalk.restartLsp", async () => {
        restartPromise ??= restartLanguageServer()
            .then(() => {
            vscode_1.window.showInformationMessage("TalkTalk language server restarted.");
        })
            .finally(() => {
            restartPromise = undefined;
        });
        return restartPromise;
    }), vscode_1.commands.registerCommand("talktalk.setCorePath", setCorePath), vscode_1.commands.registerCommand("talktalk.clearCorePath", clearCorePath));
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