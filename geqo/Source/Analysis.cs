using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Collections;
using System.Diagnostics;
using Microsoft.Boogie.VCExprAST;
using SDiff;

namespace geqo
{
    class Analysis
    {
        static private class CmdLineOptsNames
        {
            public const string debug = "/break";
        }

        static private Program program;

        static int Main(string[] args)
        {
            if (args.Length < 1)
            {
                Usage();
                return -1;
            }

            CommandLineOptions.Install(new CommandLineOptions());
            CommandLineOptions.Clo.RunningBoogieFromCommandLine = true;
            var boogieOptions = "/typeEncoding:m -timeLimit:20 -removeEmptyBlocks:0 /printModel:1 /printModelToFile:model.dmp /printInstrumented "; // /errorLimit:1";
            //IMPORTANT: need the next to avoid crash while creating prover
            CommandLineOptions.Clo.Parse(boogieOptions.Split(' '));
            //IMPORTANT: need these three to make use of UNSAT cores!!
            CommandLineOptions.Clo.UseUnsatCoreForContractInfer = true; //ROHIT
            CommandLineOptions.Clo.ContractInfer = true; //ROHIT
            CommandLineOptions.Clo.ExplainHoudini = true;

            #region Command line parsing
            if (args.Any(x => x.ToLower() == CmdLineOptsNames.debug.ToLower()))
                Debugger.Launch();
            #endregion


            var filename = args[0];
            if (!Utils.ParseProgram(filename, out program))
            {
                Usage();
                return -1;
            }

            Implementation impl = program.Implementations.First();


            if (SDiff.Boogie.Process.ResolveAndTypeCheck(program, null))
                return 1;

            SDiffCounterexamples SErrors = null;
            List<Model> errModelList = null;
            Dictionary<string, Declaration> newDict = null;


            var vcgen = BoogieVerify.InitializeVC(program);
            //SDiff.Boogie.Process.ResolveAndTypeCheck(newProg, "");
            newDict = SDiff.Boogie.Process.BuildProgramDictionary(program.TopLevelDeclarations.ToList());

            var result = BoogieVerify.VerifyImplementation(vcgen, impl, program, out SErrors, out errModelList);

            switch (result)
            {
                case VerificationResult.Error:
                    Log.Out(Log.Verifier, "Result: Error");
                    break;
                case VerificationResult.Verified:
                    Log.Out(Log.Verifier, "Result: Verified");
                    break;
                case VerificationResult.OutOfMemory:
                    Log.Out(Log.Verifier, "Result: OutOfMemory");
                    break;
                case VerificationResult.TimeOut:
                    Log.Out(Log.Verifier, "Result: TimeOut");
                    break;
                default:
                    Log.Out(Log.Verifier, "Result: Unhandled");
                    break;
            }
            vcgen.Close();


            if (result != VerificationResult.Error) return 0; //even timeouts/unhandled, as we see timeouts with 1 error, 0 model

            //process counterexamples OVER THE NEW IN-MEMORY PROGRAM
            List<Variable> outputVars = impl.OutParams;
            List<Variable> globals = impl.Proc.Modifies.Select(m => m.Decl).ToList();


            if (SErrors != null &&
                SErrors.Count > 0 &&
                errModelList.Count == SErrors.Count) //change as now SErrors can be nonnull, yet Count == 0. Sometimes model.Count < SErrror!!
            {
                PrintCounterexamples(SErrors);
            }

            return (SErrors == null ? 0 : SErrors.Count);

            /*
            //---- generate VC starts ---------
            //following unsatcoreFromFailures.cs/PerformRootcauseWorks or EqualityFixes.cs/PerformRootCause in Rootcause project
            //typecheck the instrumented program
            program.Resolve();
            program.Typecheck();

            //Generate VC
            VC.InitializeVCGen(program);
            VCExpr programVC = VC.GenerateVC(program, impl);
            //---- generate VC ends ---------

            //Should call VerifyVC before invoking CheckAssumptions
            List<Counterexample> cexs;
            //var preInp = impl.InParams
            //    .Aggregate(VCExpressionGenerator.True, (x, y) => VC.exprGen.And(x, VC.translator.LookupVariable(y)));
            //var preOut = impl.OutParams
            //    .Aggregate(VCExpressionGenerator.True, (x, y) => VC.exprGen.And(x, VC.exprGen.Not(VC.translator.LookupVariable(y))));
            //preOut = VC.exprGen.And(preOut, VC.translator.LookupVariable(outConstant));
            //var newVC = VC.exprGen.Implies(preOut, programVC);

            //var xv = VC.translator.LookupVariable(impl.LocVars.First(v => v.Name == "x"));
            //var yv = VC.translator.LookupVariable(impl.LocVars.First(v => v.Name == "y"));
            var vc = programVC;//VC.exprGen.Implies(programVC, VC.exprGen.Gt(xv, yv));
            Console.WriteLine(vc);
            //check for validity (presence of all input eq implies output is equal)
            var outcome = VC.VerifyVC("Equiv", vc, out cexs);
            //Console.WriteLine(programVC);
            Console.WriteLine("Outcome = " + outcome + " (" + cexs.Count + " counterexamples)");
            cexs.Iter(cex => cex.Print(0,Console.Out) );
            return 0;
            */

        }

        private static void Usage()
        {
            int length = 20;
            string execName = System.Diagnostics.Process.GetCurrentProcess().MainModule.ModuleName;
            Console.WriteLine("geqo.");
            Console.WriteLine("Usage: " + execName + " <filename.bpl> [flags]");
            Console.WriteLine(CmdLineOptsNames.debug.PadRight(length, ' ') + " - start in debug mode");
        }

        private static void PrintCounterexamples(SDiffCounterexamples errors)
        {
            List<Expr> constraintExprs = new List<Expr>();
            for (int i = 0; i < errors.Count; ++i)
            {
                var impl = errors[i].Impl;
                var trace = errors[i].Trace;

                var deCall = new SDiff.SymEx.DesugarCallCmds();
                trace = deCall.VisitTrace(trace);

                //symbolic constants
                var symInParams = new List<Variable>(impl.InParams); // inputs
                impl.Proc.Modifies.Iter(m => symInParams.Add(m.Decl)); // globals in the modset

                var sTrace = SDiff.SymEx.Cexecutor.ExecDown(trace, symInParams);
                SDiff.SymEx.Cexecutor.ExecUp(sTrace);
                SDiff.SymEx.CexDumper.PrintSymbolicTrace(sTrace);
            }
        }
    }
}
