//===- opt.cpp - The LLVM Modular Optimizer -------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Optimizations may be specified an arbitrary number of times on the command
// line, They are run in the order specified.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/LLVMContext.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/RegionPass.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Assembly/PrintModulePass.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/CodeGen/CommandFlags.h"
#include "llvm/DebugInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/LinkAllIR.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/MC/SubtargetFeature.h"
#include "llvm/PassManager.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PassNameParser.h"
#include "llvm/Support/PluginLoader.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <algorithm>
#include <memory>
using namespace llvm;

// The OptimizationList is automatically populated with registered Passes by the
// PassNameParser.
//
static cl::list<const PassInfo*, bool, PassNameParser>
PassList(cl::desc("Optimizations available:"));

// Other command line options...
//
static cl::opt<std::string>
InputFilename(cl::Positional, cl::desc("<input bitcode file>"),
    cl::init("-"), cl::value_desc("filename"));

static cl::opt<std::string>
OutputFilename("o", cl::desc("Override output filename"),
               cl::value_desc("filename"));

static cl::opt<bool>
Force("f", cl::desc("Enable binary output on terminals"));

static cl::opt<bool>
PrintEachXForm("p", cl::desc("Print module after each transformation"));

static cl::opt<bool>
NoOutput("disable-output",
         cl::desc("Do not write result bitcode file"), cl::Hidden);

static cl::opt<bool>
OutputAssembly("S", cl::desc("Write output as LLVM assembly"));

static cl::opt<bool>
NoVerify("disable-verify", cl::desc("Do not verify result module"), cl::Hidden);

static cl::opt<bool>
VerifyEach("verify-each", cl::desc("Verify after each transform"));

static cl::opt<bool>
StripDebug("strip-debug",
           cl::desc("Strip debugger symbol info from translation unit"));

static cl::opt<bool>
DisableInline("disable-inlining", cl::desc("Do not run the inliner pass"));

static cl::opt<bool>
DisableOptimizations("disable-opt",
                     cl::desc("Do not run any optimization passes"));

static cl::opt<bool>
DisableInternalize("disable-internalize",
                   cl::desc("Do not mark all symbols as internal"));

static cl::opt<bool>
StandardCompileOpts("std-compile-opts",
                   cl::desc("Include the standard compile time optimizations"));

static cl::opt<bool>
StandardLinkOpts("std-link-opts",
                 cl::desc("Include the standard link time optimizations"));

static cl::opt<bool>
OptLevelO1("O1",
           cl::desc("Optimization level 1. Similar to clang -O1"));

static cl::opt<bool>
OptLevelO2("O2",
           cl::desc("Optimization level 2. Similar to clang -O2"));

static cl::opt<bool>
OptLevelOs("Os",
           cl::desc("Like -O2 with extra optimizations for size. Similar to clang -Os"));

static cl::opt<bool>
OptLevelOz("Oz",
           cl::desc("Like -Os but reduces code size further. Similar to clang -Oz"));

static cl::opt<bool>
OptLevelO3("O3",
           cl::desc("Optimization level 3. Similar to clang -O3"));

static cl::opt<std::string>
TargetTriple("mtriple", cl::desc("Override target triple for module"));

static cl::opt<bool>
UnitAtATime("funit-at-a-time",
            cl::desc("Enable IPO. This is same as llvm-gcc's -funit-at-a-time"),
            cl::init(true));

static cl::opt<bool>
DisableLoopUnrolling("disable-loop-unrolling",
                     cl::desc("Disable loop unrolling in all relevant passes"),
                     cl::init(false));
static cl::opt<bool>
DisableLoopVectorization("disable-loop-vectorization",
                     cl::desc("Disable the loop vectorization pass"),
                     cl::init(false));

static cl::opt<bool>
DisableSLPVectorization("disable-slp-vectorization",
                        cl::desc("Disable the slp vectorization pass"),
                        cl::init(false));


static cl::opt<bool>
DisableSimplifyLibCalls("disable-simplify-libcalls",
                        cl::desc("Disable simplify-libcalls"));

static cl::opt<bool>
Quiet("q", cl::desc("Obsolete option"), cl::Hidden);

static cl::alias
QuietA("quiet", cl::desc("Alias for -q"), cl::aliasopt(Quiet));

static cl::opt<bool>
AnalyzeOnly("analyze", cl::desc("Only perform analysis, no optimization"));

static cl::opt<bool>
PrintBreakpoints("print-breakpoints-for-testing",
                 cl::desc("Print select breakpoints location for testing"));

static cl::opt<std::string>
DefaultDataLayout("default-data-layout",
          cl::desc("data layout string to use if not specified by module"),
          cl::value_desc("layout-string"), cl::init(""));

// ---------- Define Printers for module and function passes ------------
namespace {

struct CallGraphSCCPassPrinter : public CallGraphSCCPass {
  static char ID;
  const PassInfo *PassToPrint;
  raw_ostream &Out;
  std::string PassName;

  CallGraphSCCPassPrinter(const PassInfo *PI, raw_ostream &out) :
    CallGraphSCCPass(ID), PassToPrint(PI), Out(out) {
      std::string PassToPrintName =  PassToPrint->getPassName();
      PassName = "CallGraphSCCPass Printer: " + PassToPrintName;
    }

  virtual bool runOnSCC(CallGraphSCC &SCC) {
    if (!Quiet)
      Out << "Printing analysis '" << PassToPrint->getPassName() << "':\n";

    // Get and print pass...
    for (CallGraphSCC::iterator I = SCC.begin(), E = SCC.end(); I != E; ++I) {
      Function *F = (*I)->getFunction();
      if (F)
        getAnalysisID<Pass>(PassToPrint->getTypeInfo()).print(Out,
                                                              F->getParent());
    }
    return false;
  }

  virtual const char *getPassName() const { return PassName.c_str(); }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequiredID(PassToPrint->getTypeInfo());
    AU.setPreservesAll();
  }
};

char CallGraphSCCPassPrinter::ID = 0;

struct ModulePassPrinter : public ModulePass {
  static char ID;
  const PassInfo *PassToPrint;
  raw_ostream &Out;
  std::string PassName;

  ModulePassPrinter(const PassInfo *PI, raw_ostream &out)
    : ModulePass(ID), PassToPrint(PI), Out(out) {
      std::string PassToPrintName =  PassToPrint->getPassName();
      PassName = "ModulePass Printer: " + PassToPrintName;
    }

  virtual bool runOnModule(Module &M) {
    if (!Quiet)
      Out << "Printing analysis '" << PassToPrint->getPassName() << "':\n";

    // Get and print pass...
    getAnalysisID<Pass>(PassToPrint->getTypeInfo()).print(Out, &M);
    return false;
  }

  virtual const char *getPassName() const { return PassName.c_str(); }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequiredID(PassToPrint->getTypeInfo());
    AU.setPreservesAll();
  }
};

char ModulePassPrinter::ID = 0;
struct FunctionPassPrinter : public FunctionPass {
  const PassInfo *PassToPrint;
  raw_ostream &Out;
  static char ID;
  std::string PassName;

  FunctionPassPrinter(const PassInfo *PI, raw_ostream &out)
    : FunctionPass(ID), PassToPrint(PI), Out(out) {
      std::string PassToPrintName =  PassToPrint->getPassName();
      PassName = "FunctionPass Printer: " + PassToPrintName;
    }

  virtual bool runOnFunction(Function &F) {
    if (!Quiet)
      Out << "Printing analysis '" << PassToPrint->getPassName()
          << "' for function '" << F.getName() << "':\n";

    // Get and print pass...
    getAnalysisID<Pass>(PassToPrint->getTypeInfo()).print(Out,
            F.getParent());
    return false;
  }

  virtual const char *getPassName() const { return PassName.c_str(); }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequiredID(PassToPrint->getTypeInfo());
    AU.setPreservesAll();
  }
};

char FunctionPassPrinter::ID = 0;

struct LoopPassPrinter : public LoopPass {
  static char ID;
  const PassInfo *PassToPrint;
  raw_ostream &Out;
  std::string PassName;

  LoopPassPrinter(const PassInfo *PI, raw_ostream &out) :
    LoopPass(ID), PassToPrint(PI), Out(out) {
      std::string PassToPrintName =  PassToPrint->getPassName();
      PassName = "LoopPass Printer: " + PassToPrintName;
    }


  virtual bool runOnLoop(Loop *L, LPPassManager &LPM) {
    if (!Quiet)
      Out << "Printing analysis '" << PassToPrint->getPassName() << "':\n";

    // Get and print pass...
    getAnalysisID<Pass>(PassToPrint->getTypeInfo()).print(Out,
                        L->getHeader()->getParent()->getParent());
    return false;
  }

  virtual const char *getPassName() const { return PassName.c_str(); }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequiredID(PassToPrint->getTypeInfo());
    AU.setPreservesAll();
  }
};

char LoopPassPrinter::ID = 0;

struct RegionPassPrinter : public RegionPass {
  static char ID;
  const PassInfo *PassToPrint;
  raw_ostream &Out;
  std::string PassName;

  RegionPassPrinter(const PassInfo *PI, raw_ostream &out) : RegionPass(ID),
    PassToPrint(PI), Out(out) {
    std::string PassToPrintName =  PassToPrint->getPassName();
    PassName = "RegionPass Printer: " + PassToPrintName;
  }

  virtual bool runOnRegion(Region *R, RGPassManager &RGM) {
    if (!Quiet) {
      Out << "Printing analysis '" << PassToPrint->getPassName() << "' for "
          << "region: '" << R->getNameStr() << "' in function '"
          << R->getEntry()->getParent()->getName() << "':\n";
    }
    // Get and print pass...
   getAnalysisID<Pass>(PassToPrint->getTypeInfo()).print(Out,
                       R->getEntry()->getParent()->getParent());
    return false;
  }

  virtual const char *getPassName() const { return PassName.c_str(); }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequiredID(PassToPrint->getTypeInfo());
    AU.setPreservesAll();
  }
};

char RegionPassPrinter::ID = 0;

struct BasicBlockPassPrinter : public BasicBlockPass {
  const PassInfo *PassToPrint;
  raw_ostream &Out;
  static char ID;
  std::string PassName;

  BasicBlockPassPrinter(const PassInfo *PI, raw_ostream &out)
    : BasicBlockPass(ID), PassToPrint(PI), Out(out) {
      std::string PassToPrintName =  PassToPrint->getPassName();
      PassName = "BasicBlockPass Printer: " + PassToPrintName;
    }

  virtual bool runOnBasicBlock(BasicBlock &BB) {
    if (!Quiet)
      Out << "Printing Analysis info for BasicBlock '" << BB.getName()
          << "': Pass " << PassToPrint->getPassName() << ":\n";

    // Get and print pass...
    getAnalysisID<Pass>(PassToPrint->getTypeInfo()).print(Out,
            BB.getParent()->getParent());
    return false;
  }

  virtual const char *getPassName() const { return PassName.c_str(); }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequiredID(PassToPrint->getTypeInfo());
    AU.setPreservesAll();
  }
};

char BasicBlockPassPrinter::ID = 0;

struct BreakpointPrinter : public ModulePass {
  raw_ostream &Out;
  static char ID;
  DITypeIdentifierMap TypeIdentifierMap;

  BreakpointPrinter(raw_ostream &out)
    : ModulePass(ID), Out(out) {
    }

  void getContextName(DIDescriptor Context, std::string &N) {
    if (Context.isNameSpace()) {
      DINameSpace NS(Context);
      if (!NS.getName().empty()) {
        getContextName(NS.getContext(), N);
        N = N + NS.getName().str() + "::";
      }
    } else if (Context.isType()) {
      DIType TY(Context);
      if (!TY.getName().empty()) {
        getContextName(TY.getContext().resolve(TypeIdentifierMap), N);
        N = N + TY.getName().str() + "::";
      }
    }
  }

  virtual bool runOnModule(Module &M) {
    TypeIdentifierMap.clear();
    NamedMDNode *CU_Nodes = M.getNamedMetadata("llvm.dbg.cu");
    if (CU_Nodes)
      TypeIdentifierMap = generateDITypeIdentifierMap(CU_Nodes);

    StringSet<> Processed;
    if (NamedMDNode *NMD = M.getNamedMetadata("llvm.dbg.sp"))
      for (unsigned i = 0, e = NMD->getNumOperands(); i != e; ++i) {
        std::string Name;
        DISubprogram SP(NMD->getOperand(i));
        assert((!SP || SP.isSubprogram()) &&
          "A MDNode in llvm.dbg.sp should be null or a DISubprogram.");
        if (!SP)
          continue;
        getContextName(SP.getContext().resolve(TypeIdentifierMap), Name);
        Name = Name + SP.getDisplayName().str();
        if (!Name.empty() && Processed.insert(Name)) {
          Out << Name << "\n";
        }
      }
    return false;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
  }
};

} // anonymous namespace

char BreakpointPrinter::ID = 0;

static inline void addPass(PassManagerBase &PM, Pass *P) {
  // Add the pass to the pass manager...
  PM.add(P);

  // If we are verifying all of the intermediate steps, add the verifier...
  if (VerifyEach) PM.add(createVerifierPass());
}

/// AddOptimizationPasses - This routine adds optimization passes
/// based on selected optimization level, OptLevel. This routine
/// duplicates llvm-gcc behaviour.
///
/// OptLevel - Optimization Level
static void AddOptimizationPasses(PassManagerBase &MPM,FunctionPassManager &FPM,
                                  unsigned OptLevel, unsigned SizeLevel) {
  FPM.add(createVerifierPass());                  // Verify that input is correct

  PassManagerBuilder Builder;
  Builder.OptLevel = OptLevel;
  Builder.SizeLevel = SizeLevel;

  if (DisableInline) {
    // No inlining pass
  } else if (OptLevel > 1) {
    unsigned Threshold = 225;
    if (SizeLevel == 1)      // -Os
      Threshold = 75;
    else if (SizeLevel == 2) // -Oz
      Threshold = 25;
    if (OptLevel > 2)
      Threshold = 275;
    Builder.Inliner = createFunctionInliningPass(Threshold);
  } else {
    Builder.Inliner = createAlwaysInlinerPass();
  }
  Builder.DisableUnitAtATime = !UnitAtATime;
  Builder.DisableUnrollLoops = (DisableLoopUnrolling.getNumOccurrences() > 0) ?
                               DisableLoopUnrolling : OptLevel == 0;

  Builder.LoopVectorize =
      DisableLoopVectorization ? false : OptLevel > 1 && SizeLevel < 2;
  Builder.SLPVectorize =
      DisableSLPVectorization ? false : OptLevel > 1 && SizeLevel < 2;

  Builder.populateFunctionPassManager(FPM);
  Builder.populateModulePassManager(MPM);
}

static void AddStandardCompilePasses(PassManagerBase &PM) {
  PM.add(createVerifierPass());                  // Verify that input is correct

  // If the -strip-debug command line option was specified, do it.
  if (StripDebug)
    addPass(PM, createStripSymbolsPass(true));

  if (DisableOptimizations) return;

  // -std-compile-opts adds the same module passes as -O3.
  PassManagerBuilder Builder;
  if (!DisableInline)
    Builder.Inliner = createFunctionInliningPass();
  Builder.OptLevel = 3;
  Builder.populateModulePassManager(PM);
}

static void AddStandardLinkPasses(PassManagerBase &PM) {
  PM.add(createVerifierPass());                  // Verify that input is correct

  // If the -strip-debug command line option was specified, do it.
  if (StripDebug)
    addPass(PM, createStripSymbolsPass(true));

  if (DisableOptimizations) return;

  PassManagerBuilder Builder;
  Builder.populateLTOPassManager(PM, /*Internalize=*/ !DisableInternalize,
                                 /*RunInliner=*/ !DisableInline);
}

//===----------------------------------------------------------------------===//
// CodeGen-related helper functions.
//
static TargetOptions GetTargetOptions() {
  TargetOptions Options;
  Options.LessPreciseFPMADOption = EnableFPMAD;
  Options.NoFramePointerElim = DisableFPElim;
  Options.AllowFPOpFusion = FuseFPOps;
  Options.UnsafeFPMath = EnableUnsafeFPMath;
  Options.NoInfsFPMath = EnableNoInfsFPMath;
  Options.NoNaNsFPMath = EnableNoNaNsFPMath;
  Options.HonorSignDependentRoundingFPMathOption =
  EnableHonorSignDependentRoundingFPMath;
  Options.UseSoftFloat = GenerateSoftFloatCalls;
  if (FloatABIForCalls != FloatABI::Default)
    Options.FloatABIType = FloatABIForCalls;
  Options.NoZerosInBSS = DontPlaceZerosInBSS;
  Options.GuaranteedTailCallOpt = EnableGuaranteedTailCallOpt;
  Options.DisableTailCalls = DisableTailCalls;
  Options.StackAlignmentOverride = OverrideStackAlignment;
  Options.TrapFuncName = TrapFuncName;
  Options.PositionIndependentExecutable = EnablePIE;
  Options.EnableSegmentedStacks = SegmentedStacks;
  Options.UseInitArray = UseInitArray;
  return Options;
}

CodeGenOpt::Level GetCodeGenOptLevel() {
  if (OptLevelO1)
    return CodeGenOpt::Less;
  if (OptLevelO2)
    return CodeGenOpt::Default;
  if (OptLevelO3)
    return CodeGenOpt::Aggressive;
  return CodeGenOpt::None;
}

// Returns the TargetMachine instance or zero if no triple is provided.
static TargetMachine* GetTargetMachine(Triple TheTriple) {
  std::string Error;
  const Target *TheTarget = TargetRegistry::lookupTarget(MArch, TheTriple,
                                                         Error);
  // Some modules don't specify a triple, and this is okay.
  if (!TheTarget) {
    return 0;
  }

  // Package up features to be passed to target/subtarget
  std::string FeaturesStr;
  if (MAttrs.size()) {
    SubtargetFeatures Features;
    for (unsigned i = 0; i != MAttrs.size(); ++i)
      Features.AddFeature(MAttrs[i]);
    FeaturesStr = Features.getString();
  }

  return TheTarget->createTargetMachine(TheTriple.getTriple(),
                                        MCPU, FeaturesStr, GetTargetOptions(),
                                        RelocModel, CMModel,
                                        GetCodeGenOptLevel());
}

//===----------------------------------------------------------------------===//
// main for opt
//
int main(int argc, char **argv) {
  sys::PrintStackTraceOnErrorSignal();
  llvm::PrettyStackTraceProgram X(argc, argv);

  // Enable debug stream buffering.
  EnableDebugBuffering = true;

  llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.
  LLVMContext &Context = getGlobalContext();



  cl::ParseCommandLineOptions(argc, argv,
    "llvm .bc -> .bc modular optimizer and analysis printer\n");

  if (AnalyzeOnly && NoOutput) {
    errs() << argv[0] << ": analyze mode conflicts with no-output mode.\n";
    return 1;
  }

  SMDiagnostic Err;

  // Load the input module...
  OwningPtr<Module> M;
  M.reset(ParseIRFile(InputFilename, Err, Context));

  if (M.get() == 0) {
    Err.print(argv[0], errs());
    return 1;
  }

  // Figure out what stream we are supposed to write to...
  OwningPtr<tool_output_file> Out;
  if (NoOutput) {
    if (!OutputFilename.empty())
      errs() << "WARNING: The -o (output filename) option is ignored when\n"
                "the --disable-output option is used.\n";
  } else {
    // Default to standard output.
    if (OutputFilename.empty())
      OutputFilename = "-";

    std::string ErrorInfo;
    Out.reset(new tool_output_file(OutputFilename.c_str(), ErrorInfo,
                                   sys::fs::F_Binary));
    if (!ErrorInfo.empty()) {
      errs() << ErrorInfo << '\n';
      return 1;
    }
  }


  PassManager Passes;


  // Create a new optimization pass for each one specified on the command line
  for (unsigned i = 0; i < PassList.size(); ++i) {
    // Check to see if -std-compile-opts was specified before this option.  If
    // so, handle it.
    const PassInfo *PassInf = PassList[i];
    Pass *P = 0;
    if (PassInf->getNormalCtor())
      P = PassInf->getNormalCtor()();
    else
      errs() << argv[0] << ": cannot create pass: "
             << PassInf->getPassName() << "\n";
    if (P) {
      PassKind Kind = P->getPassKind();
      addPass(Passes, P);


    }
  }

  // Before executing passes, print the final values of the LLVM options.
  cl::PrintOptionValues();

  // Now that we have all of the passes ready, run them.
  Passes.run(*M.get());

  // Declare success.
  if (!NoOutput || PrintBreakpoints)
    Out->keep();

  return 0;
}
