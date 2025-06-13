"use strict";
/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
exports.deactivate = deactivate;
const vscode_1 = require("vscode");
const node_1 = require("vscode-languageclient/node");
let client;
function activate(context) {
    // If the extension is launched in debug mode then the debug server options are used
    // Otherwise the run options are used
    const serverOptions = {
        command: "/Users/nakajima/apps/talk-rs/target/debug/talk",
        transport: node_1.TransportKind.stdio,
        args: ["lsp"],
        options: {
            env: {
                RUST_LOG: "debug",
            },
        },
    };
    // Options to control the language client
    const clientOptions = {
        // Register the server for plain text documents
        documentSelector: [{ scheme: "file", language: "talktalk" }],
        synchronize: {
            // Notify the server about file changes to '.clientrc files contained in the workspace
            fileEvents: vscode_1.workspace.createFileSystemWatcher("**/.clientrc"),
        },
    };
    // Create the language client and start the client.
    client = new node_1.LanguageClient("TalkTalk", "TalkTalk Language Server", serverOptions, clientOptions);
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