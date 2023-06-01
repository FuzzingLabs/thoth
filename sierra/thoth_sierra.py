import time
from sierra import config
from sierra.analyzer import all_analyzers
from sierra.analyzer.abstract_analyzer import category_classification_text
from sierra.arguments import parse_thoth_checker_arguments, parse_thoth_sierra_arguments
from sierra.callgraph.callgraph import SierraCallGraph
from sierra.decompiler.decompiler import SierraDecompiler
from sierra.parser.parser import SierraParser
from sierra.symbex.symbex import SierraSymbolicExecution
from sierra.utils import colors


def thoth_sierra() -> None:
    """
    thoth-sierra command entry point
    """

    args = parse_thoth_sierra_arguments()

    # Output color
    colors.__init__(color=not args.no_colors)

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
            return

    # Parse a Sierra file
    sierra_file = args.file
    if sierra_file is None:
        print("You need to specify a sierra file path using the -f flag")
        return

    try:
        parser = SierraParser(config.SIERRA_LARK_PARSER_PATH)
        parser.parse(sierra_file)
    except Exception:
        print("%s is not a valid sierra file" % sierra_file)
        return

    # Control-Flow Graph
    if args.cfg:
        parser.print_cfg(folder=args.output_cfg_folder, file_format=args.format, view=False)
        return

    # Call-Graph
    if args.call:
        callgraph = SierraCallGraph(parser)
        callgraph.generate_callgraph()

        callgraph.print_callgraph(
            folder=args.output_callgraph_folder, file_format=args.format, view=False
        )
        return

    if args.symbolic:
        if args.function is None:
            print(
                "Symbolic execution: You need to set the -function flag e.g. -function __main__.main"
            )
            functions_list = [f.id for f in parser.functions]
            print("\nPossible values:\n\t%s" % ("\n\t".join(functions_list)))
            return

        # Function parameter
        symbex_function = args.function
        try:
            function = [f for f in parser.functions if f.id == symbex_function][0]
        except:
            print("Symbolic execution: Function %s doesn't exist" % symbex_function)
            return 1

        if not args.solves:
            print("Symbolic execution: You need to set the -solve flag, e.g. -solves v1 v2 v3")
            return 1
        if not args.constraints:
            print(
                "Symbolic execution: You need to set the -constraints flag e.g. - constraints v1==0 v2==0"
            )
            return 1

        symbex_constraints = args.constraints
        symbex_solves = args.solves
        symbex_variables = args.variables

        symbolic_execution = SierraSymbolicExecution(function=function)
        solve = symbolic_execution.solve(
            constraints=symbex_constraints, solves=symbex_solves, variables_values=symbex_variables
        )

        if solve:
            for variable in solve:
                print("%s: %s" % (variable[0], variable[1]))
        else:
            print("No solution")
        return

    # Decompiler output
    if args.decompile:
        decompiler = SierraDecompiler(program=parser)
        decompiled_code = decompiler.decompile_code()
        print(decompiled_code)
        return

    if args.analyzers is None:
        return

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
        a = analyzer(parser)
        if a._detect():
            detected = True
            detected_analyzers_count += 1
        a.print()
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


def thoth_checker() -> None:
    """
    thoth-checker command entry point
    """
    # Output color
    colors.__init__(color=True)

    args = parse_thoth_checker_arguments()

    print("[+] Thoth Symbolic bounded model checker\n")

    # Parse a Sierra file
    sierra_file = args.file
    if sierra_file is None:
        print("You need to specify a sierra file path using the -f flag")
        return

    try:
        parser = SierraParser(config.SIERRA_LARK_PARSER_PATH)
        parser.parse(sierra_file)
    except:
        print("%s is not a valid sierra file" % sierra_file)
        return

    test_functions = [f for f in parser.functions if f.id.split("::")[-1].startswith("thoth_test")]

    for i in range(len(test_functions)):
        function = test_functions[i]

        symbolic_execution = SierraSymbolicExecution(function=function)

        start_time = time.time()
        solve, paths = symbolic_execution.solve_test_function()
        solve_duration = round(time.time() - start_time, 2)

        if solve:
            result = colors.GREEN + "PASS" + colors.ENDC
        else:
            result = colors.RED + "FAIL" + colors.ENDC

        print(
            "[%s] %s (test %s/%s, time: %ss, paths: %s)"
            % (result, function.id, i + 1, len(test_functions), solve_duration, paths)
        )
    return
