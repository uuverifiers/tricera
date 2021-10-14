#pragma once

#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/TypeVisitor.h"

#include "TriCeraPreprocessorMain.hpp"

class MainConsumer : public clang::ASTConsumer {
public:
  MainConsumer(clang::Rewriter &rewriter,
               PreprocessOutput &out) : 
               rewriter(rewriter), preprocessOutput(out) {}
  void HandleTranslationUnit(clang::ASTContext& Ctx) override;
  ~MainConsumer() override;

private:
  clang::Rewriter &rewriter;
  PreprocessOutput &preprocessOutput;
};
