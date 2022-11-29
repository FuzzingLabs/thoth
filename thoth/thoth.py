import os
import sys
import tempfile
from thoth.app.decompiler.decompiler import Decompiler
from thoth.app.dfg.dfg import DFG
from thoth.app.symbex.symbex import SymbolicExecution
from thoth.app.utils import str_to_bool
from thoth.app.arguments import parse_args
from thoth.app.analyzer import all_analyzers
from thoth.app.analyzer.abstract_analyzer import category_classification_text
from thoth.app.disassembler.disassembler import Disassembler
from thoth.app.starknet.starknet import StarkNet


def main() -> int:
    """Main function of Thoth

    Returns:
        Int: Return 0
    """
    args = parse_args()
    if (args.call or args.cfg or args.dfg) and ("view" not in args):
        print("Need to set -view option")
        sys.exit()

    # Show analyzers help
    if args.analyzers_help is not None:
        if args.analyzers_help:
            for analyzer_name in args.analyzers_help:
                analyzer = [
                    analyzer for analyzer in all_analyzers if analyzer.ARGUMENT == analyzer_name
                ][0]
                analyzer._print_help()
            return 0
        else:
            for analyzer in all_analyzers:
                analyzer._print_help()
            return 0

    # Load compiled contract from a file
    if args.contract == "local":
        file = args.path.name
        filename = os.path.basename(args.path.name).split(".")[0]
    # Load compiled contract from starknet API
    else:
        try:
            contract = StarkNet(args.network).get_full_contract(args.address)
        except Exception as e:
            print(e)
            exit()
        file = tempfile.NamedTemporaryFile().name
        with open(file, "w") as f:
            f.write(contract)
        filename = args.address

    disassembler = Disassembler(file, color=args.color)

    if args.verbose:
        disassembler.dump_json()

    # Decompiler
    if args.decompile and args.analyzers is None:
        print(disassembler.decompiler())
        if args.output:
            output = Disassembler(file, color=False).decompiler()
            with args.output as output_file:
                output_file.write(output)
    # Disassembler
    elif args.disassembly and args.analyzers is None:
        print(disassembler.print_disassembly())
        if args.output:
            output = Disassembler(file, color=False).print_disassembly()
            with args.output as output_file:
                output_file.write(output)

    format = "pdf" if args.format is None else str(args.format)

    # Print the call flow graph
    if args.call:
        disassembler.print_call_flow_graph(
            folder=args.output_callgraph_folder,
            filename=filename,
            format=format,
            view=str_to_bool(args.view),
        )

    # Print the CFG
    if args.cfg:
        if args.color:
            disassembler = Disassembler(file, color=False)
        disassembler.print_cfg(
            folder=args.output_cfg_folder,
            filename=filename,
            format=format,
            function_name=args.function,
            view=str_to_bool(args.view),
        )

    # Print the DFG
    if args.dfg:
        contract_functions = disassembler.functions
        decompiler = Decompiler(functions=contract_functions)
        decompiler.decompile_code(first_pass_only=True)

        dfg = DFG(decompiler.ssa.memory)
        dfg._create_dfg()
        if args.taint:
            dfg._taint_functions_arguments()
        dfg._create_graph_representation()
        dfg._print_dfg(
            view=str_to_bool(args.view), folder=args.output_dfg_folder, format=args.format
        )

    # Symbolic execution
    if args.symbolic:

        # Mandatory arguments (function, solve, constraint)
        if args.function is None:
            print(
                "Symbolic execution: You need to set the -function flag e.g. -function __main__.main"
            )
            functions_list = [f.name for f in disassembler.functions]
            print("\nPossible values:\n\t%s" % ("\n\t".join(functions_list)))
            return 1
        if not args.solve:
            print("Symbolic execution: You need to set the -solve flag, e.g. -solve v1 v2 v3")
            return 1
        if not args.constraint:
            print(
                "Symbolic execution: You need to set the -constraint flag e.g. - constraint v1==0 v2==0"
            )

        contract_functions = disassembler.functions
        decompiler = Decompiler(functions=contract_functions)
        decompiler.decompile_code(first_pass_only=True)

        symbex = SymbolicExecution(decompiler.ssa.memory)

        try:
            function = [f for f in disassembler.functions if f.name == args.function][0]
        except:
            return 1
        solve = symbex._solve(
            function=function,
            constraints=args.constraint,
            variables_values=args.variables,
            solves=args.solve,
        )
        if solve:
            for variable in solve:
                print("%s: %s" % (variable[0], variable[1]))
        else:
            print("No solution")
        return 0

    if args.analyzers is None:
        return 0

    # Find selected analyzers
    analyzers_names = [analyzer.ARGUMENT for analyzer in all_analyzers]
    selected_analyzers = []

    if args.analyzers:
        selected_analyzers = []
        for analyzer_name in args.analyzers:
            # Select a single analyzer
            if analyzer_name in analyzers_names:
                selected_analyzers.append(
                    [analyzer for analyzer in all_analyzers if analyzer.ARGUMENT == analyzer_name][
                        0
                    ]
                )
            # Select a whole category
            else:
                selected_category = [
                    k
                    for k, v in category_classification_text.items()
                    if v == analyzer_name.capitalize()
                ][0]
                selected_analyzers += [
                    analyzer for analyzer in all_analyzers if analyzer.CATEGORY == selected_category
                ]
    # Select all analyzers by default
    else:
        selected_analyzers = all_analyzers

    # Run analyzers
    detected_analyzers_count = 0
    for analyzer in selected_analyzers:
        detected = False
        a = analyzer(disassembler, color=args.color)
        if a._detect():
            detected = True
            detected_analyzers_count += 1
        a._print()
        if detected:
            print()

    selected_analyzers_count = len(selected_analyzers)

    print(
        "[+] %s analyzer%s %s run (%s detected)"
        % (
            selected_analyzers_count,
            "s" if selected_analyzers_count > 1 else "",
            "were" if selected_analyzers_count > 1 else "was",
            detected_analyzers_count,
        )
    )
    return 0
