#include "TriceraPreprocessor.hpp"

#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include <unistd.h>
#include <fcntl.h>

#include "llvm/Support/CommandLine.h"
#include <string.h>

using namespace llvm;
using namespace clang;
using namespace tooling;

//===----------------------------------------------------------------------===//
// Command line options
//===----------------------------------------------------------------------===//
static cl::OptionCategory TPCategory("tricera-preprocessor options");
cl::opt<std::string> outputFilename("o", 
                                    cl::desc("Specify output absolute path (required)"), 
                                    cl::value_desc("output file absolute path"), 
                                    cl::cat(TPCategory), cl::Required);
cl::opt<bool> quiet ("q", cl::desc("Suppress error and warning messages"), 
                     cl::cat(TPCategory));


//===----------------------------------------------------------------------===//
// PluginASTAction
//===----------------------------------------------------------------------===//
class TriCeraPreprocessAction : public clang::ASTFrontendAction {
public:
  TriCeraPreprocessAction(PreprocessOutput &out) :
    preprocessOutput(out) {}

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef file) override {
    rewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return std::make_unique<MainConsumer>(rewriter, preprocessOutput);
  }

  void EndSourceFileAction() override {
    SourceManager &sm = rewriter.getSourceMgr();
    std::error_code error_code;
    raw_fd_ostream outFile(outputFilename.c_str(), error_code, sys::fs::F_None);
    rewriter.getEditBuffer(sm.getMainFileID()).write(outFile);
    outFile.close();
  }

PreprocessOutput &preprocessOutput;
private:
  clang::Rewriter rewriter;
  StringRef inFile;
};

std::unique_ptr<FrontendActionFactory> 
  newTPFrontendActionFactory(PreprocessOutput &out) {
  class TPFrontendActionFactory : public FrontendActionFactory {
  public:
    TPFrontendActionFactory(PreprocessOutput &out) : 
                            out(out) {}
    std::unique_ptr<FrontendAction> create() override {
      return std::make_unique<TriCeraPreprocessAction>(out);
    }
  private:
    PreprocessOutput &out;
  };

  return std::unique_ptr<FrontendActionFactory>(
      new TPFrontendActionFactory(out));
}

int main(int argc, const char **argv) {
  clang::tooling::CommonOptionsParser OptionsParser(argc, argv, TPCategory);
  clang::tooling::ClangTool tool(OptionsParser.getCompilations(),
                                 OptionsParser.getSourcePathList());
  
  // suppress stderr output
  int fd, n;
  if (quiet) {
    fd = dup(2);
    n = open("/dev/null", O_WRONLY);
    dup2(n, 2);
    close(n);
  }

  PreprocessOutput preprocessOutput;
  preprocessOutput.hasErrorOccurred = 
    tool.run(newTPFrontendActionFactory(preprocessOutput).get()) != 0;

  if (quiet) {
    dup2(fd, 2); // restore stderr output
    close(fd);
  }

  return preprocessOutput.hasErrorOccurred;
}
