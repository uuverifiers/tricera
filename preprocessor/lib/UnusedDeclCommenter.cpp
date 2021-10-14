#include "UnusedDeclCommenter.hpp"
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


using namespace clang;
using namespace ast_matchers;
using namespace llvm;

UnusedDeclCommenter::UnusedDeclCommenter(clang::Rewriter &r, clang::ASTContext &Ctx, 
                      UsedFunAndTypeCollector &usedFunsAndTypes) {
    UnusedDeclCommenterASTConsumer c(r, usedFunsAndTypes);
    c.HandleTranslationUnit(Ctx);
}

UnusedDeclCommenterASTConsumer::UnusedDeclCommenterASTConsumer(clang::Rewriter &r,
                                     UsedFunAndTypeCollector &usedFunsAndTypes)
                           : handler(rewriter, usedFunsAndTypes), rewriter(r) {
  DeclarationMatcher usedDeclMatcher = 
  anyOf(
    // comment out unused function decls
    functionDecl(unless(isImplicit())).bind("functionDecl"), 
    // comment out unused record decls
    recordDecl().bind("recordDecl"), 
    // comment out var decls using records,
    varDecl(
      unless(parmVarDecl()), // unless they are fun args
      anyOf(
        hasDescendant(qualType(hasCanonicalType(
          qualType(anyOf(recordType(), enumType())).bind("varBaseType")))),
        hasType(qualType(arrayType()).bind("varBaseType"))
      )
    ).bind("varDecl")
    // more?
  );
    
  finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource, 
                             usedDeclMatcher), &handler);
}

void UnusedDeclCommenterMatcher::run(const MatchFinder::MatchResult &Result) {
  ASTContext *Ctx = Result.Context;

  const RecordDecl * recordDecl = 
    Result.Nodes.getNodeAs<clang::RecordDecl>("recordDecl"); 

  const FunctionDecl * functionDecl =
    Result.Nodes.getNodeAs<clang::FunctionDecl>("functionDecl"); 
  
  const VarDecl * varDecl =
    Result.Nodes.getNodeAs<clang::VarDecl>("varDecl"); 

  if (functionDecl) 
  { // comment out unused function declarations
    if (!usedFunsAndTypes.functionIsSeen(functionDecl))
      doubleSlashCommentOutDeclaration(functionDecl, *Ctx, rewriter);
  } 
  else if (recordDecl) 
  { // comment out unused record declarations
    if (!usedFunsAndTypes.typeIsSeen(
        Ctx->getTypeDeclType(recordDecl).getTypePtr()))
      doubleSlashCommentOutDeclaration(recordDecl, *Ctx, rewriter);
  }
  else if (varDecl) 
  { // comment out unused var declarations
    // note that this might comment out some record declarations
    // several times if the vars are declared as part of the
    // record declaration: e.g. struct s {...} s1;
    const QualType * varBaseType =
      Result.Nodes.getNodeAs<clang::QualType>("varBaseType"); 
    if (!usedFunsAndTypes.typeIsSeen(varBaseType))
      doubleSlashCommentOutDeclaration(varDecl, *Ctx, rewriter);
  }
  else {
    llvm_unreachable("UnusedDeclCommenter unreachable case\n");
  }
}
