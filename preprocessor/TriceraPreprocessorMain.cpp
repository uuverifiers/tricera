#include "TriceraPreprocessor.hpp"

#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include <unistd.h>
#include <fcntl.h>

using namespace llvm;
using namespace clang;
using namespace tooling;

//===----------------------------------------------------------------------===//
// Command line options
//===----------------------------------------------------------------------===//
static llvm::cl::OptionCategory TPCategory("tricera-preprocessor options");

//===----------------------------------------------------------------------===//
// PluginASTAction
//===----------------------------------------------------------------------===//
class TriCeraPreprocessAction : public clang::ASTFrontendAction {
public:
  TriCeraPreprocessAction(PreprocessOutput &out, 
                          const char *outputFileAbsolutePath) :
    preprocessOutput(out), outPath(outputFileAbsolutePath) {}

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef file) override {
    rewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return std::make_unique<MainConsumer>(rewriter, preprocessOutput);
  }

  void EndSourceFileAction() override {
    SourceManager &sm = rewriter.getSourceMgr();
    std::error_code error_code;
    raw_fd_ostream outFile(outPath, error_code, sys::fs::F_None);
    rewriter.getEditBuffer(sm.getMainFileID()).write(outFile);
    outFile.close();
  }

PreprocessOutput &preprocessOutput;
const char *outPath;

private:
  clang::Rewriter rewriter;
  StringRef inFile;
};

/*class TPPluginAction : public PluginASTAction {
public:
  bool ParseArgs(const CompilerInstance &CI,
                 const std::vector<std::string> &args) override {
    return true;
  }

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef file) override {
    rewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return std::make_unique<MainConsumer>(rewriter);
  }

private:
  Rewriter rewriter;
};*/

std::unique_ptr<FrontendActionFactory> 
  newTPFrontendActionFactory(PreprocessOutput &out,
                             const char *outputFileAbsolutePath) {
  class TPFrontendActionFactory : public FrontendActionFactory {
  public:
    TPFrontendActionFactory(PreprocessOutput &out,
                            const char *outPath) : 
                            out(out), outPath(outPath) {}
    std::unique_ptr<FrontendAction> create() override {
      return std::make_unique<TriCeraPreprocessAction>(
        out, outPath);
    }
  private:
    PreprocessOutput &out;
    const char *outPath;
  };

  return std::unique_ptr<FrontendActionFactory>(
      new TPFrontendActionFactory(out, outputFileAbsolutePath));
}

PreprocessOutput runTool(int argc, const char **argv, 
                         const char *outputFileAbsolutePath) {
  clang::tooling::CommonOptionsParser OptionsParser(argc, argv, TPCategory);
  clang::tooling::ClangTool tool(OptionsParser.getCompilations(),
                                 OptionsParser.getSourcePathList());  
  
  // suppress stderr output
  int fd = dup(2);
  int n = open("/dev/null", O_WRONLY);
  dup2(n, 2);
  close(n);

  PreprocessOutput preprocessOutput;
  preprocessOutput.hasErrorOccurred = 
    tool.run(newTPFrontendActionFactory(preprocessOutput, 
                                        outputFileAbsolutePath).get()) != 0;
  dup2(fd, 2); // restore stderr output
  close(fd);
  
  return preprocessOutput;
}