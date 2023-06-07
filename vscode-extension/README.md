## Thoth Visual Studio code extension

The thoth extension allows you to use thoth functions directly in Visual Studio Code.

### How to install

#### Create the **.vsix** package
```bash
# Install vscm in npm 
npm install -g vsce

# Clone and open the repository
git clone https://github.com/FuzzingLabs/thoth.git
cd ./thoth/github-actions

# Output a 'thoth-vscode-x.x.x.vsix' in the folder
vsce package
```
#### Install the extension

To install it on your Visual Studio Code, navigate to the extension page and click on the three-dot icon. Then select  "*Install from VSIX*" and specify the location of the .vsix file you created in the previous step.

### Usage

When you have a Sierra file or a JSON artifact open in VS Code, you can select the commands to launch with a **right click**

<p align="center">
  <img src="https://raw.githubusercontent.com/FuzzingLabs/thoth/master/vscode-extension/doc/run-commands-buttons.png" />
</p>

Available commands for Sierra files: 
- `Run thoth-sierra decompiler` to output the decompiled version of a Sierra file.
- `Run thoth-sierra analyzers` to output the analyzers results on a Sierra file.
- `Run thoth-sierra CFG` to output the CFG of a Sierra file.
- `Run thoth-sierra callgraph` to output the CallGraph of a Sierra file.

Available commands for Cairo JSON artifacts
- `Run thoth decompiler` to output the decompiled version of a Cairo JSON artifact.
- `Run thoth disassembler` to output the CallGraph of a Cairo JSON artifact.
- `Run thoth analyzers` to output the analyzers results on a Cairo JSON artifact.
- `Run thoth CFG` to output the CFG of a Cairo JSON artifact.
- `Run thoth callgraph` to output the CallGraph of a Cairo JSON artifact.
