#pragma once

#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/TypeVisitor.h"

#include "UsedFunctionAndTypeCollector.hpp"

class TypedefMatcher : 
  public clang::ast_matchers::MatchFinder::MatchCallback {
public:
  TypedefMatcher(clang::Rewriter &rewriter, 
    UsedFunAndTypeCollector &usedFunsAndTypes) : rewriter(rewriter), 
                                          usedFunsAndTypes(usedFunsAndTypes) {}
  // this callback executes on a match
  void run(const clang::ast_matchers::MatchFinder::MatchResult &) override;
  
  // this callback executes at the end of the translation unit
  void onEndOfTranslationUnit() override{};

  private:
  clang::Rewriter &rewriter;
  llvm::SmallSet<clang::SourceLocation, 32> EditedLocations;
  UsedFunAndTypeCollector &usedFunsAndTypes;
};

class TypedefRemoverASTConsumer : public clang::ASTConsumer {
public:
  TypedefRemoverASTConsumer(clang::Rewriter &rewriter,
                            UsedFunAndTypeCollector &usedFunsAndTypes);
  void HandleTranslationUnit(clang::ASTContext &Ctx) override {
    finder.matchAST(Ctx);
  }
private:
  clang::ast_matchers::MatchFinder finder;
  TypedefMatcher handler;
  clang::Rewriter &rewriter;
};

// collects all seen functions and types on construction
class TypedefRemover {
  public:
  TypedefRemover(clang::Rewriter &rewriter, clang::ASTContext &Ctx, 
                 UsedFunAndTypeCollector &usedFunsAndTypes) {
    TypedefRemoverASTConsumer c(rewriter, usedFunsAndTypes);
    c.HandleTranslationUnit(Ctx);
  }
};
