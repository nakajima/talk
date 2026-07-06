/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import { existsSync } from "fs";
import { homedir } from "os";
import {
  commands,
  ConfigurationTarget,
  ExtensionContext,
  Uri,
  window,
  workspace,
} from "vscode";

import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient/node";

let client: LanguageClient;
let restartPromise: Promise<void> | undefined;

function expandHome(path: string): string {
  if (path === "~") {
    return homedir();
  }

  if (path.startsWith("~/")) {
    return homedir() + path.slice(1);
  }

  return path;
}

function configuredCorePath(): string | undefined {
  const corePath = workspace
    .getConfiguration("talktalk")
    .get<string>("corePath")
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

function configuredStdlibPath(): string | undefined {
  const stdlibPath = workspace
    .getConfiguration("talktalk")
    .get<string>("stdlibPath")
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

function serverOptions(): ServerOptions {
  const corePath = configuredCorePath();
  const stdlibPath = configuredStdlibPath();
  const env = {
    ...process.env,
    RUST_LOG: process.env.RUST_LOG ?? "debug",
    ...(corePath ? { TALK_CORE_PATH: corePath } : {}),
    ...(stdlibPath ? { TALK_STDLIB_PATH: stdlibPath } : {}),
  };

  return {
    command: homedir() + "/apps/talk/target/debug/talk",
    transport: TransportKind.stdio,
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

let createClient: () => LanguageClient;

async function setCorePath() {
  const current = configuredCorePath();
  const devCorePath = homedir() + "/apps/talk/core";
  const defaultPath = current ?? (existsSync(devCorePath) ? devCorePath : homedir());
  const selected = await window.showOpenDialog({
    canSelectFiles: false,
    canSelectFolders: true,
    canSelectMany: false,
    defaultUri: Uri.file(defaultPath),
    openLabel: "Use as TALK_CORE_PATH",
    title: "Select Talk core directory",
  });

  const folder = selected?.[0]?.fsPath;
  if (!folder) {
    return;
  }

  const target = workspace.workspaceFolders?.length
    ? ConfigurationTarget.Workspace
    : ConfigurationTarget.Global;
  await workspace.getConfiguration("talktalk").update("corePath", folder, target);

  const restart = await window.showInformationMessage(
    `TalkTalk core path set to ${folder}.`,
    "Restart Language Server"
  );
  if (restart === "Restart Language Server") {
    await commands.executeCommand("talktalk.restartLsp");
  }
}

async function clearCorePath() {
  const target = workspace.workspaceFolders?.length
    ? ConfigurationTarget.Workspace
    : ConfigurationTarget.Global;
  await workspace.getConfiguration("talktalk").update("corePath", undefined, target);

  const restart = await window.showInformationMessage(
    "TalkTalk core path cleared.",
    "Restart Language Server"
  );
  if (restart === "Restart Language Server") {
    await commands.executeCommand("talktalk.restartLsp");
  }
}

async function setStdlibPath() {
  const current = configuredStdlibPath();
  const devStdlibPath = homedir() + "/apps/talk/stdlib";
  const defaultPath = current ?? (existsSync(devStdlibPath) ? devStdlibPath : homedir());
  const selected = await window.showOpenDialog({
    canSelectFiles: false,
    canSelectFolders: true,
    canSelectMany: false,
    defaultUri: Uri.file(defaultPath),
    openLabel: "Use as TALK_STDLIB_PATH",
    title: "Select Talk stdlib directory",
  });

  const folder = selected?.[0]?.fsPath;
  if (!folder) {
    return;
  }

  const target = workspace.workspaceFolders?.length
    ? ConfigurationTarget.Workspace
    : ConfigurationTarget.Global;
  await workspace.getConfiguration("talktalk").update("stdlibPath", folder, target);

  const restart = await window.showInformationMessage(
    `TalkTalk stdlib path set to ${folder}.`,
    "Restart Language Server"
  );
  if (restart === "Restart Language Server") {
    await commands.executeCommand("talktalk.restartLsp");
  }
}

async function clearStdlibPath() {
  const target = workspace.workspaceFolders?.length
    ? ConfigurationTarget.Workspace
    : ConfigurationTarget.Global;
  await workspace.getConfiguration("talktalk").update("stdlibPath", undefined, target);

  const restart = await window.showInformationMessage(
    "TalkTalk stdlib path cleared.",
    "Restart Language Server"
  );
  if (restart === "Restart Language Server") {
    await commands.executeCommand("talktalk.restartLsp");
  }
}

export function activate(context: ExtensionContext) {
  // Options to control the language client
  const clientOptions: LanguageClientOptions = {
    // Register the server for plain text documents
    documentSelector: [{ scheme: "file", language: "talktalk" }],
    synchronize: {
      // Notify the server about file changes to '.clientrc files contained in the workspace
      fileEvents: workspace.createFileSystemWatcher("**/*.tlk"),
    },
  };

  createClient = () =>
    new LanguageClient(
      "TalkTalk",
      "TalkTalk Language Server",
      serverOptions(),
      clientOptions
    );

  context.subscriptions.push(
    commands.registerCommand("talktalk.restartLsp", async () => {
      restartPromise ??= restartLanguageServer()
        .then(() => {
          window.showInformationMessage("TalkTalk language server restarted.");
        })
        .finally(() => {
          restartPromise = undefined;
        });

      return restartPromise;
    }),
    commands.registerCommand("talktalk.setCorePath", setCorePath),
    commands.registerCommand("talktalk.clearCorePath", clearCorePath),
    commands.registerCommand("talktalk.setStdlibPath", setStdlibPath),
    commands.registerCommand("talktalk.clearStdlibPath", clearStdlibPath)
  );

  // Create the language client and start the client.
  client = createClient();

  // Start the client. This will also launch the server
  client.start();
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
