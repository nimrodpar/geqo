﻿﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.IO;
using System.Diagnostics;
using Microsoft.Boogie.VCExprAST;
using VC;
using Microsoft.Basetypes;
using BType = Microsoft.Boogie.Type;

namespace geqo
{
    static class Utils
    {

        public static bool ParseProgram(string fname, out Program prog)
        {
            prog = null;
            int errCount;
            try
            {
                errCount = Parser.Parse(fname, new List<string>(), out prog);
                if (errCount != 0 || prog == null)
                {
                    Console.WriteLine("WARNING: {0} parse errors detected in {1}", errCount, fname);
                    return false;
                }
            }
            catch (IOException e)
            {
                Console.WriteLine("WARNING: Error opening file \"{0}\": {1}", fname, e.Message);
                return false;
            }
            errCount = prog.Resolve();
            if (errCount > 0)
            {
                Console.WriteLine("WARNING: {0} name resolution errors in {1}", errCount, fname);
                return false;
            }
            ModSetCollector c = new ModSetCollector();
            c.DoModSetAnalysis(prog);
            errCount = prog.Typecheck();
            if (errCount > 0)
            {
                Console.WriteLine("WARNING: {0} type checking errors in {1}", errCount, fname);
                return false;
            }
            return true;
        }
    }

    //state related to VC generation that will be shared by different options
    /// <summary>
    /// TODO: Copied from Rootcause, refactor
    /// </summary>
    static class VC
    {
        /* vcgen related state */
        static public VCGen vcgen;
        static public ProverInterface proverInterface;
        static public ProverInterface.ErrorHandler handler;
        static public ConditionGeneration.CounterexampleCollector collector;
        static public Boogie2VCExprTranslator translator;
        static public VCExpressionGenerator exprGen;

        #region Utilities for calling the verifier
        public static void InitializeVCGen(Program prog)
        {
            //create VC.vcgen/VC.proverInterface
            VC.vcgen = new VCGen(prog, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, null);
            VC.proverInterface = ProverInterface.CreateProver(prog, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, CommandLineOptions.Clo.ProverKillTime);
            VC.translator = VC.proverInterface.Context.BoogieExprTranslator;
            VC.exprGen = VC.proverInterface.Context.ExprGen;
            VC.collector = new ConditionGeneration.CounterexampleCollector();
        }
        public static ProverInterface.Outcome VerifyVC(string descriptiveName, VCExpr vc, out List<Counterexample> cex)
        {
            VC.collector.examples.Clear(); //reset the cexs
            //Use MyBeginCheck instead of BeginCheck as it is inconsistent with CheckAssumptions's Push/Pop of declarations
            ProverInterface.Outcome proverOutcome;
            //proverOutcome = MyBeginCheck(descriptiveName, vc, VC.handler); //Crashes now
            VC.proverInterface.BeginCheck(descriptiveName, vc, VC.handler);
            proverOutcome = VC.proverInterface.CheckOutcome(VC.handler);
            cex = VC.collector.examples;
            return proverOutcome;
        }

        public static void FinalizeVCGen(Program prog)
        {
            VC.collector = null;
        }

        public static ProverInterface.Outcome MyBeginCheck(string descriptiveName, VCExpr vc, ProverInterface.ErrorHandler handler)
        {
            VC.proverInterface.Push();
            VC.proverInterface.Assert(vc, true);
            VC.proverInterface.Check();
            var outcome = VC.proverInterface.CheckOutcomeCore(VC.handler);
            VC.proverInterface.Pop();
            return outcome;
        }
        public static VCExpr GenerateVC(Program prog, Implementation impl)
        {
            VC.vcgen.ConvertCFG2DAG(impl);
            ModelViewInfo mvInfo;
            var /*TransferCmd->ReturnCmd*/ gotoCmdOrigins = VC.vcgen.PassifyImpl(impl, out mvInfo);

            var exprGen = VC.proverInterface.Context.ExprGen;
            //VCExpr controlFlowVariableExpr = null; 
            VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : VC.exprGen.Integer(BigNum.ZERO);


            Dictionary<int, Absy> label2absy;
            var vc = VC.vcgen.GenerateVC(impl, controlFlowVariableExpr, out label2absy, VC.proverInterface.Context);
            if (!CommandLineOptions.Clo.UseLabels)
            {
                VCExpr controlFlowFunctionAppl = VC.exprGen.ControlFlowFunctionApplication(VC.exprGen.Integer(BigNum.ZERO), VC.exprGen.Integer(BigNum.ZERO));
                VCExpr eqExpr = VC.exprGen.Eq(controlFlowFunctionAppl, VC.exprGen.Integer(BigNum.FromInt(impl.Blocks[0].UniqueId)));
                vc = VC.exprGen.Implies(eqExpr, vc);
            }

            if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Local)
            {
                VC.handler = new VCGen.ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, VC.vcgen.incarnationOriginMap, VC.collector, mvInfo, VC.proverInterface.Context, prog);
            }
            else
            {
                VC.handler = new VCGen.ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, VC.vcgen.incarnationOriginMap, VC.collector, mvInfo, VC.proverInterface.Context, prog);
            }
            return vc;
        }
        #endregion

    }

}
