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

  const runSierraCallgraph = vscode.commands.registerCommand('extension.runThothSierraCallGraph', () => {
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

  // Create a new panel and set its content
  const panel = vscode.window.createWebviewPanel(
    'thothSierraDecompiler',
    'Thoth Sierra Decompiler',
    vscode.ViewColumn.Beside,
    {}
  );

  // Run the thoth command on the file and update the panel content
  const { spawn } = require('child_process');
  const thothProcess = spawn('thoth-sierra', ['-f', filePath, '-d']);

  let output = '';
  thothProcess.stdout.on('data', (data: string) => {
    output += data;
    panel.webview.html = output;
  });

  thothProcess.stderr.on('data', (data: string) => {
    output += data;
    panel.webview.html = output;
  });

  thothProcess.on('close', (code: number) => {
    if (code !== 0) {
      output += `Thoth Sierra Analyzer exited with code ${code}.`;
      panel.webview.html = output;
    }
  });

  panel.onDidDispose(() => {
    thothProcess.kill();
  });
}

function runThothSierraAnalyzer() {
  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new panel and set its content
  const panel = vscode.window.createWebviewPanel(
    'thothSierraAnalyzer',
    'Thoth Sierra Analyzer',
    vscode.ViewColumn.Beside,
    {}
  );

  // Run the thoth command on the file and update the panel content
  const { spawn } = require('child_process');
  const thothProcess = spawn('thoth-sierra', ['-f', filePath, '-a']);

  let output = '';
  thothProcess.stdout.on('data', (data: string) => {
    output += data;
    panel.webview.html = output;
  });

  thothProcess.stderr.on('data', (data: string) => {
    output += data;
    panel.webview.html = output;
  });

  thothProcess.on('close', (code: number) => {
    if (code !== 0) {
      output += `Thoth Sierra Analyzer exited with code ${code}.`;
      panel.webview.html = output;
    }
  });

  panel.onDidDispose(() => {
    thothProcess.kill();
  });
}

function runThothSierraCFG() {
  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new panel and set its content
  const panel = vscode.window.createWebviewPanel(
    'thothSierraCFG',
    'Thoth Sierra CFG',
    vscode.ViewColumn.Beside,
    {}
  );

  // Run the thoth command on the file and update the panel content
  const { spawn } = require('child_process');
  const thothProcess = spawn('thoth-sierra', ['-f', filePath, '--cfg', '-output_cfg_folder', '/tmp/cfgoutput', '--format', 'png']);
  
  let output = '';

  const imagePath = '/tmp/cfgoutput/cfg.gv.png';
  const onDiskPath = vscode.Uri.file(imagePath);
  const imageUri = panel.webview.asWebviewUri(onDiskPath);
  output += `<img src="${imageUri}" alt="${onDiskPath.path}"/>`;
  
  panel.webview.html = output;

  thothProcess.stderr.on('data', (data: string) => {
    output += data;
    panel.webview2 = output;
  });

  thothProcess.on('close', (code: number) => {
    if (code !== 0) {
      output += `Thoth Sierra Analyzer exited with code ${code}.`;
      panel.webview.html = output;
    }
  });

  panel.onDidDispose(() => {
    thothProcess.kill();
  });
}


function runThothSierraCallGraph() {
  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new panel and set its content
  const panel = vscode.window.createWebviewPanel(
    'thothSierraCallGraph',
    'Thoth Sierra CallGraph',
    vscode.ViewColumn.Beside,
    {}
  );

  // Run the thoth command on the file and update the panel content
  const { spawn } = require('child_process');
  const thothProcess = spawn('thoth-sierra', ['-f', filePath, '--call', '-output_callgraph_folder', '/tmp/callgraphoutput', '--format', 'png']);
  
  let output = '';

  const imagePath = '/tmp/callgraphoutput/cfg.gv.png';
  const onDiskPath = vscode.Uri.file(imagePath);
  const imageUri = panel.webview.asWebviewUri(onDiskPath);
  output += `<img src="${imageUri}" alt="${onDiskPath.path}"/>`;
  
  panel.webview.html = output;

  thothProcess.stderr.on('data', (data: string) => {
    output += data;
    panel.webview2 = output;
  });

  thothProcess.on('close', (code: number) => {
    if (code !== 0) {
      output += `Thoth Sierra Analyzer exited with code ${code}.`;
      panel.webview.html = output;
    }
  });

  panel.onDidDispose(() => {
    thothProcess.kill();
  });
}


function deactivate() {}

module.exports = {
  activate,
  deactivate
};

function getWebviewContent(arg0: any) {
  throw new Error("Function not implemented.");
}
