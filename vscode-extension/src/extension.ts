const vscode = require('vscode');
const cp = require('child_process');

function activate(context: { subscriptions: any[]; }) {
  const runSierraDecompilerCommand = vscode.commands.registerCommand('extension.runThothSierraDecompiler', () => {
    runThothSierraDecompiler();
  });

  const runSierraAnalyzerCommand = vscode.commands.registerCommand('extension.runThothSierraAnalyzer', () => {
    runThothSierraAnalyzer();
  });

  const runSierraCFG = vscode.commands.registerCommand('extension.runThothSierraCFG', () => {
    runThothSierraCFG();
  });

  const runSierraCallgraph = vscode.commands.registerCommand('extension.runThothSierraCallgraph', () => {
    runThothSierraCallGraph();
  });

  context.subscriptions.push(runSierraDecompilerCommand, runSierraAnalyzerCommand);
}

function runThothSierraDecompiler() {
  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new terminal and run the thoth command on the file
  const terminal = vscode.window.createTerminal('Thoth');
  terminal.sendText(`thoth-sierra -f "${filePath}" -d`, true);
  terminal.show();
}

function runThothSierraAnalyzer() {
  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new terminal and run the thoth command on the file
  const terminal = vscode.window.createTerminal('Thoth');
  terminal.sendText(`thoth-sierra -f "${filePath}" -a`, true);
  terminal.show();
}

function runThothSierraCFG() {
  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new terminal and run the thoth command on the file
  const terminal = vscode.window.createTerminal('Thoth');
  terminal.sendText(`thoth-sierra -f "${filePath}" --cfg`, true);
  terminal.show();
}

function runThothSierraCallGraph() {
  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new terminal and run the thoth command on the file
  const terminal = vscode.window.createTerminal('Thoth');
  terminal.sendText(`thoth-sierra -f "${filePath}" --call`, true);
  terminal.show();
}


function deactivate() {}

module.exports = {
  activate,
  deactivate
};