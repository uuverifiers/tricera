// Replaces all (used) types appearing in the AST with their canonical versions.
// A type visitor (TypeCanoniser) is used for this purpose, which tries to
// extract the canonical type from a given type.
// e.g. typedef struct A* B; 
//      "B* x" is canonised to "struct A** x"

#pragma once

#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/TypeVisitor.h"

#include "UsedFunctionAndTypeCollector.hpp"

class TypeCanoniserMatcher : 
  public clang::ast_matchers::MatchFinder::MatchCallback {
public:
  TypeCanoniserMatcher(clang::Rewriter &r, 
                  UsedFunAndTypeCollector &usedFunsAndTypes)
                  : rewriter(r), usedFunsAndTypes(usedFunsAndTypes) {}
  // this callback executes on a match
  void run(const clang::ast_matchers::MatchFinder::MatchResult &) override;
  
  // this callback executes at the end of the translation unit
  void onEndOfTranslationUnit() override{};

private:
  clang::Rewriter &rewriter;
  llvm::SmallSet<clang::SourceLocation, 32> editedLocations;
  UsedFunAndTypeCollector &usedFunsAndTypes;
};

class TypeCanoniserASTConsumer : public clang::ASTConsumer {
public:
  TypeCanoniserASTConsumer(clang::Rewriter &r, 
                           UsedFunAndTypeCollector &usedFunsAndTypes);
  void HandleTranslationUnit(clang::ASTContext &Ctx) override;
private:
  clang::ast_matchers::MatchFinder finder;
  TypeCanoniserMatcher handler;
  clang::Rewriter &rewriter;
};

// collects all seen functions and types on construction
class TypeCanoniser {
  public:
  TypeCanoniser(clang::Rewriter &r, clang::ASTContext &Ctx, 
                UsedFunAndTypeCollector &usedFunsAndTypes) {
    TypeCanoniserASTConsumer c(r, usedFunsAndTypes);
    c.HandleTranslationUnit(Ctx);
  }
};

// AST Visitors
class TypeCanoniserVisitor
: public clang::RecursiveASTVisitor<TypeCanoniserVisitor> {
public:
  explicit TypeCanoniserVisitor(clang::ASTContext &Ctx) : Ctx(Ctx) {
    unqualType = clang::QualType();
  }

    bool shouldTraversePostOrder() const { return true; }
    bool VisitType(clang::Type *typ);
    bool VisitConstantArrayType(clang::ConstantArrayType *typ);
    clang::QualType getUnqualType() { return unqualType; }

    std::string getUnqualifiedTypeName() const {
      return (unqualTypeName + std::string(numPointers, '*')); 
    }
    std::string getUnqualifiedTypeNameWithoutPtrs() const {
      return unqualTypeName; 
    }
    std::string getOnlyPtrs() const {
      return std::string(numPointers, '*');
    }
    bool isFunctionType() const { return isFunctionPrototype; }
    bool convertedArrayToPtr() const { return _convertedArrayToPtr; }
    std::string getFunctionPtrTypeFullName(std::string funName) const {
      return (functionReturnTypeName + 
        " (" + std::string(numPointers, '*') + funName + ") " +
        unqualTypeName); 
    }
  
  private:
    clang::ASTContext &Ctx;
    clang::QualType unqualType;
    std::string unqualTypeName = ""; // set by VisitType after traversal
    std::string functionReturnTypeName = "";
    int numPointers = 0;
    bool isFunctionPrototype = false;
    bool _convertedArrayToPtr = false; // true when converted T x[1] to T* x
};