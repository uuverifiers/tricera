#include "TriceraPreprocessor.hpp"

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/Lex/Lexer.h"
#include "clang/AST/PrettyPrinter.h"

#include "UsedFunctionAndTypeCollector.hpp"
#include "TypedefRemover.hpp"
#include "UnusedDeclCommenter.hpp"
#include "TypeCanoniser.hpp"
#include "ForLoopStmtExtractor.hpp"

using namespace clang;
using namespace ast_matchers;
using namespace std;

#include <string>

//-----------------------------------------------------------------------------
//
//-----------------------------------------------------------------------------
void MainConsumer::HandleTranslationUnit(clang::ASTContext& Ctx) {
  
  // todo: process files where an error has occurred?
  // errors also occur on some inputs which TriCera would accept
  bool hadError = Ctx.getDiagnostics().hasErrorOccurred();
  bool collectAllFuns = hadError;
  bool collectAllTypes = hadError;
  // todo: or return without doing anything?
  // if (Ctx.getDiagnostics().hasErrorOccurred()) return;
  
   // collect all used functions and types
  UsedFunAndTypeCollector usedFunsAndTypes(Ctx, collectAllFuns, 
                                           collectAllTypes);
   // then remove all typedefs and remove unused record typedef declarations
  TypedefRemover typedefRemover(rewriter, Ctx, usedFunsAndTypes);
   // then comment out all unused declarations
  if (!hadError)
    UnusedDeclCommenter declCommenter(rewriter, Ctx, usedFunsAndTypes);
   // and canonise all used types
  TypeCanoniser typeCanoniser(rewriter, Ctx, usedFunsAndTypes);
  // extract declStmts from inside for loop declarations
  ForLoopStmtExtractor forLoopStmtExtractor(rewriter, Ctx, usedFunsAndTypes);
  
   // finally add contract annotations to recursive functions
  preprocessOutput.numRecursiveFuns = 0;
  for (auto funInfo : usedFunsAndTypes.getSeenFunctions()) {
    if (funInfo->isRecursive()) {
      auto decl = funInfo->getDecl();
      if (decl->hasBody()) { // todo: ignore decls without bodies?
        rewriter.InsertTextBefore(decl->getBeginLoc(),
                                  "/*@ contract @*/ ");
        preprocessOutput.numRecursiveFuns ++;
      }    
    }
  }

  preprocessOutput.usesArrays = 0;
  for (const Type* typ : usedFunsAndTypes.getSeenTypes()) {
    if (typ->isArrayType())
      preprocessOutput.usesArrays = 1;
  }

  // todo: set this to 1 if any unsupported features exist
  preprocessOutput.isUnsupported = 0;

  // todo: any string to pass to output?
  std::string s = "foo";
  preprocessOutput.outputBuffer = new char[s.length()];
  std::strcpy(preprocessOutput.outputBuffer, s.c_str());
  
  //llvm::outs() << "--------------------------\n";
  //llvm::outs() << "Seen functions:\n";
  //llvm::outs() << "--------------------------\n";
  //for (auto funInfo : usedFunsAndTypes.getSeenFunctions()) {
  //  llvm::outs() << funInfo->getDecl()->getNameAsString();
  //  if(funInfo->isRecursive())
  //    llvm::outs() << " (recursive)";
  //  llvm::outs() << "\n";
  //}
  //llvm::outs() << "--------------------------\n";
  //llvm::outs() << "Seen types:\n";
  //llvm::outs() << "--------------------------\n";
  //for (const Type* typ : usedFunsAndTypes.getSeenTypes()) {
  //  typ->dump();
  //}
  //rewriter.getEditBuffer(rewriter.getSourceMgr().getMainFileID())
  //    .write(llvm::outs());
}

MainConsumer::~MainConsumer() {
  // any cleanup?
}
