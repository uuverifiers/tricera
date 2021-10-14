#include "ForLoopStmtExtractor.hpp"
#include "Utilities.hpp"

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/TypeVisitor.h"

#include "llvm/Support/raw_ostream.h"
#include <string>


using namespace clang;
using namespace ast_matchers;
using namespace llvm;

ForLoopStmtExtractor::ForLoopStmtExtractor(clang::Rewriter &r, clang::ASTContext &Ctx, 
                      UsedFunAndTypeCollector &usedFunsAndTypes) {
    ForLoopStmtExtractorASTConsumer c(r, usedFunsAndTypes);
    c.HandleTranslationUnit(Ctx);
}

ForLoopStmtExtractorASTConsumer::ForLoopStmtExtractorASTConsumer(clang::Rewriter &r,
                                     UsedFunAndTypeCollector &usedFunsAndTypes)
                           : handler(rewriter, usedFunsAndTypes), rewriter(r) {
  StatementMatcher forLoopDeclStmtMatcher = 
    declStmt(hasParent(forStmt().bind("forStmt"))).bind("declStmt");
    // todo: comment out only if enclosing function is seen?
    
  finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource, 
                             forLoopDeclStmtMatcher), &handler);
}

void ForLoopStmtExtractorMatcher::run(const MatchFinder::MatchResult &Result) {
  ASTContext *Ctx = Result.Context;

  const ForStmt * forStmt = 
    Result.Nodes.getNodeAs<clang::ForStmt>("forStmt"); 

  const DeclStmt * declStmt =
    Result.Nodes.getNodeAs<clang::DeclStmt>("declStmt"); 

  if (forStmt && declStmt) 
  { // get the decl. text from inside the for loop and move it before the loop
    rewriter.InsertTextBefore(forStmt->getBeginLoc(), 
      "{ " + rewriter.getRewrittenText(declStmt->getSourceRange()) + " "
    );
    // comment out the decl. inside the for loop
    wrapWithCComment(declStmt->getSourceRange(), rewriter);
    // close the compound stmt after the loop
    rewriter.InsertTextAfter(forStmt->getEndLoc(), "}");
  } else {
    llvm_unreachable("ForLoopStmtExtractor unreachable case\n");
  }
}
