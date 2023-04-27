const vscode = require('vscode');
const cp = require('child_process');

function replaceColors(data: string) {
  /**
   * Replaces ANSI color codes with HTML span tags for styling
   * @param {string} data - The string to replace the color codes in
   * @returns {string} The updated string with HTML span tags
   */

  // Convert data to a string if it's not already
  data = String(data);
  
  // Define color code mappings
  const colorMap = {
    "\x1b[95m": "<span style='color:#EBD8B2' >",
    "\x1b[94m": "<span style='color:#6C9BCF' >",
    "\x1b[96m": "<span style='color:#A5C0DD' >",
    "\x1b[92m": "<span style='color:#98D8AA' >",
    "\x1b[93m": "<span style='color:#F7D060' >",
    "\x1b[35m": "<span style='color:#917FB3' >",
    "\x1b[91m": "<span style='color:#D21312' >",
    "\x1b[0m": "</span>",
    "\x1b[1m": "",
    "\x1b[36m": "",
    "\x1b[4m": "",
  };

  // Replace color codes with HTML span tags
  Object.entries(colorMap).forEach(([colorCode, htmlTag]) => {
    data = data.replaceAll(colorCode, htmlTag);
  });

  return data;
}

function activate(context: { subscriptions: any[]; }) {
  /**
   * Activates the extension
   * @param {vscode.ExtensionContext} context - The extension context object
   */

  // Register thoth-sierra commands
  const runSierraDecompilerCommand = vscode.commands.registerCommand('extension.runThothSierraDecompiler', runThothSierraDecompiler);
  const runSierraAnalyzerCommand = vscode.commands.registerCommand('extension.runThothSierraAnalyzer', runThothSierraAnalyzer);
  const runSierraCFGCommand = vscode.commands.registerCommand('extension.runThothSierraCFG', runThothSierraCFG);
  const runSierraCallgraphCommand = vscode.commands.registerCommand('extension.runThothSierraCallGraph', runThothSierraCallGraph);

  // Register thoth commands
  const runThothDecompilerCommand = vscode.commands.registerCommand('extension.runThothDecompiler', runThothDecompiler);
  const runThothDisassemblerCommand = vscode.commands.registerCommand('extension.runThothDisassembler', runThothDisassembler);
  const runThothAnalyzerCommand = vscode.commands.registerCommand('extension.runThothAnalyzer', runThothAnalyzer);
  const runThothCFGCommand = vscode.commands.registerCommand('extension.runThothCFG', runThothCFG);
  const runThothCallGraphCommand = vscode.commands.registerCommand('extension.runThothCallGraph', runThothCallGraph);

  // Add commands to subscriptions array
  context.subscriptions.push(
    runSierraDecompilerCommand,
    runSierraAnalyzerCommand,
    runSierraCFGCommand,
    runSierraCallgraphCommand,
    runThothDecompilerCommand,
    runThothDisassemblerCommand,
    runThothAnalyzerCommand,
    runThothCFGCommand,
    runThothCallGraphCommand
  );
}

function runThothSierraDecompiler() {
  /**
   * Runs Thoth Sierra Decompiler on the currently opened file
   */

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
    data = replaceColors(data.toString());
    output += `<pre><code>${data}</code></pre>`;
    panel.webview.html = output;
  });

  thothProcess.stderr.on('data', (data: { toString: () => string; }) => {
    output += data.toString();
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
  /**
   * Runs Thoth Sierra Analyzers on the currently opened file
   */

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
    data = replaceColors(data);
    output += data;
    panel.webview.html = `<pre><code>${output}</code></pre>`;
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
  /**
   * Runs Thoth Sierra CFG on the currently opened file
   */

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
    {
      localResourceRoots: [vscode.Uri.file('/tmp/cfgoutput/')]
    }
  );

  // Run the thoth command on the file and update the panel content
  const { spawn } = require('child_process');
  const thothProcess = spawn('thoth-sierra', ['-f', filePath, '--cfg', '-output_cfg_folder', '/tmp/cfgoutput', '--format', 'png']);
  
  let output = '';

  const imagePath = '/tmp/cfgoutput/cfg.gv.png';
  const onDiskPath = vscode.Uri.file(imagePath);
  const imageUri = panel.webview.asWebviewUri(onDiskPath).toString();
  console.log(imageUri);
  output += `<img src="${imageUri}" alt="${onDiskPath.path}"/>`;
  
  panel.webview.html = output;

  thothProcess.stderr.on('exit', (data: string) => {
    output += data;
    panel.webview.html = output;
  });

  thothProcess.on('close', (code: number) => {
    if (code !== 0) {
      output += `Thoth Sierra CFG exited with code ${code}.`;
      panel.webview.html = output;
    }
  });

  panel.onDidDispose(() => {
    thothProcess.kill();
  });
}


function runThothSierraCallGraph() {
  /**
   * Runs Thoth Sierra Callgraph on the currently opened file
   */

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
    {
      localResourceRoots: [vscode.Uri.file('/tmp/callgraphoutput/')]
    }
  );

  // Run the thoth command on the file and update the panel content
  const { spawn } = require('child_process');
  const thothProcess = spawn('thoth-sierra', ['-f', filePath, '--call', '-output_callgraph_folder', '/tmp/callgraphoutput', '--format', 'png']);
  
  let output = '';

  const imagePath = '/tmp/callgraphoutput/Call-Flow\ Graph.gv.png';
  const onDiskPath = vscode.Uri.file(imagePath);
  const imageUri = panel.webview.asWebviewUri(onDiskPath);
  output += `<img src="${imageUri}" alt="${onDiskPath.path}"/>`;
  
  panel.webview.html = output;

  thothProcess.stderr.on('exit', (data: string) => {
    output += data;
    panel.webview.html = output;
  });

  thothProcess.on('close', (code: number) => {
    if (code !== 0) {
      output += `Thoth Sierra Callgraph exited with code ${code}.`;
      panel.webview.html = output;
    }
  });

  panel.onDidDispose(() => {
    thothProcess.kill();
  });
}

function runThothDecompiler() {
  /**
   * Runs Thoth Decompiler on the currently opened file
   */

  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new panel and set its content
  const panel = vscode.window.createWebviewPanel(
    'thothDecompiler',
    'Thoth Decompiler',
    vscode.ViewColumn.Beside,
    {}
  );

  // Run the thoth command on the file and update the panel content
  const { spawn } = require('child_process');
  const thothProcess = spawn('thoth', ['local', filePath, '-d', '--color']);

  let output = '';
  thothProcess.stdout.on('data', (data: string) => {
    data = replaceColors(data.toString());
    output += `<pre><code>${data}</code></pre>`;
    panel.webview.html = output;
  });

  thothProcess.stderr.on('data', (data: { toString: () => string; }) => {
    output += data.toString();
    panel.webview.html = output;
  });

  thothProcess.on('close', (code: number) => {
    if (code !== 0) {
      output += `Thoth Decompiler exited with code ${code}.`;
      panel.webview.html = output;
    }
  });

  panel.onDidDispose(() => {
    thothProcess.kill();
  });
}

function runThothDisassembler() {
  /**
   * Runs Thoth Disassembler on the currently opened file
   */

  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new panel and set its content
  const panel = vscode.window.createWebviewPanel(
    'thothDisassembler',
    'Thoth Disassembler',
    vscode.ViewColumn.Beside,
    {}
  );

  // Run the thoth command on the file and update the panel content
  const { spawn } = require('child_process');
  const thothProcess = spawn('thoth', ['local', filePath, '-b', '--color']);

  let output = '';
  thothProcess.stdout.on('data', (data: string) => {
    data = replaceColors(data.toString());
    output += `<pre><code>${data}</code></pre>`;
    panel.webview.html = output;
  });

  thothProcess.stderr.on('data', (data: { toString: () => string; }) => {
    output += data.toString();
    panel.webview.html = output;
  });

  thothProcess.on('close', (code: number) => {
    if (code !== 0) {
      output += `Thoth Disassembler exited with code ${code}.`;
      panel.webview.html = output;
    }
  });

  panel.onDidDispose(() => {
    thothProcess.kill();
  });
}

function runThothAnalyzer() {
  /**
   * Runs Thoth Analyzers on the currently opened file
   */

  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new panel and set its content
  const panel = vscode.window.createWebviewPanel(
    'thothAnalyzer',
    'Thoth Analyzers',
    vscode.ViewColumn.Beside,
    {}
  );

  // Run the thoth command on the file and update the panel content
  const { spawn } = require('child_process');
  const thothProcess = spawn('thoth', ['local', filePath, '-a', '--color']);

  let output = '';
  thothProcess.stdout.on('data', (data: string) => {
    data = replaceColors(data.toString());
    output += `<pre><code>${data}</code></pre>`;
    panel.webview.html = output;
  });

  thothProcess.stderr.on('data', (data: { toString: () => string; }) => {
    output += data.toString();
    panel.webview.html = output;
  });

  thothProcess.on('close', (code: number) => {
    if (code !== 0) {
      output += `Thoth Analyzers exited with code ${code}.`;
      panel.webview.html = output;
    }
  });

  panel.onDidDispose(() => {
    thothProcess.kill();
  });
}

function runThothCFG() {
  /**
   * Runs Thoth CFG on the currently opened file
   */

  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new panel and set its content
  const panel = vscode.window.createWebviewPanel(
    'thothCFG',
    'Thoth CFG',
    vscode.ViewColumn.Beside,
    {
      localResourceRoots: [vscode.Uri.file('/tmp/cfgoutput/')]
    }
  );

  // Run the thoth command on the file and update the panel content
  const { spawn } = require('child_process');
  const thothProcess = spawn('thoth', ['local', filePath, '--cfg', '-output_cfg_folder', '/tmp/cfgoutput', '--format', 'png']);
  
  let output = '';

  const fileNameWithExtension = filePath.split("/").pop(); 
  const fileName = fileNameWithExtension.split(".")[0];
  const imagePath = `/tmp/cfgoutput/${fileName}.gv.png`;
  const onDiskPath = vscode.Uri.file(imagePath);
  const imageUri = panel.webview.asWebviewUri(onDiskPath).toString();
  output += `<img src="${imageUri}" alt="${onDiskPath.path}"/>`;
  
  panel.webview.html = output;

  thothProcess.stderr.on('exit', (data: string) => {
    output += data;
    panel.webview.html = output;
  });

  thothProcess.on('close', (code: number) => {
    if (code !== 0) {
      output += `Thoth CFG exited with code ${code}.`;
      panel.webview.html = output;
    }
  });

  panel.onDidDispose(() => {
    thothProcess.kill();
  });
}

function runThothCallGraph() {
  /**
   * Runs Thoth Callgraph on the currently opened file
   */

  // Get the currently opened file
  const activeEditor = vscode.window.activeTextEditor;
  if (!activeEditor) {
    vscode.window.showErrorMessage("No active editor found.");
    return;
  }
  const filePath = activeEditor.document.uri.fsPath;

  // Create a new panel and set its content
  const panel = vscode.window.createWebviewPanel(
    'thothCallGraph',
    'Thoth CallGraph',
    vscode.ViewColumn.Beside,
    {
      localResourceRoots: [vscode.Uri.file('/tmp/callgraphoutput/')]
    }
  );

  // Run the thoth command on the file and update the panel content
  const { spawn } = require('child_process');
  const thothProcess = spawn('thoth', ['local', filePath, '--call', '-output_callgraph_folder', '/tmp/callgraphoutput', '--format', 'png']);
  
  let output = '';

  const fileNameWithExtension = filePath.split("/").pop(); 
  const fileName = fileNameWithExtension.split(".")[0];
  const imagePath = `/tmp/callgraphoutput/${fileName}.gv.png`;
  const onDiskPath = vscode.Uri.file(imagePath);
  const imageUri = panel.webview.asWebviewUri(onDiskPath).toString();
  output += `<img src="${imageUri}" alt="${onDiskPath.path}"/>`;
  
  panel.webview.html = output;

  thothProcess.stderr.on('exit', (data: string) => {
    output += data;
    panel.webview.html = output;
  });

  thothProcess.on('close', (code: number) => {
    if (code !== 0) {
      output += `Thoth Callgraph exited with code ${code}.`;
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
