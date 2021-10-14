#pragma once

#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/TypeVisitor.h"

class FunctionInfo {
  private:
    const clang::FunctionDecl* _f;
    bool _isRecursive;
  public:
    FunctionInfo(const clang::FunctionDecl *f, bool isRecursive = false) :
                        _f(f), _isRecursive(isRecursive) {}
    bool isRecursive() const { return _isRecursive; }
    void setRecursive() { _isRecursive = true; }
    const clang::FunctionDecl* getDecl() const { return _f; }
};

class FindFunctionMatcher : 
  public clang::ast_matchers::MatchFinder::MatchCallback {
public:
  FindFunctionMatcher(llvm::SetVector<FunctionInfo*> &seenFunctions,
                      llvm::SetVector<const clang::Type*> &seenTypes,
                      bool collectAllFuns)  :
                      seenFunctions(seenFunctions), seenTypes(seenTypes),
                      collectAllFuns(collectAllFuns){}
  // this callback executes on a match
  void run(const clang::ast_matchers::MatchFinder::MatchResult &) override;
  
  // this callback executes at the end of the translation unit
  void onEndOfTranslationUnit() override{};

private:
  llvm::SetVector<FunctionInfo*> &seenFunctions;
  llvm::SetVector<const clang::Type*> &seenTypes;
  bool collectAllFuns;
};

// todo: this handler is a bit unnecessary, could be done in a simpler way
// since its only job is to find the main and call subHandler
class FindEntryFunctionMatcher : 
  public clang::ast_matchers::MatchFinder::MatchCallback {
public:
  FindEntryFunctionMatcher(llvm::SetVector<FunctionInfo*> &seenFunctions,
                           llvm::SetVector<const clang::Type*> &seenTypes,
                           bool collectAllFuns) 
                           : subHandler(seenFunctions, seenTypes, 
                                        collectAllFuns),
                           seenFunctions(seenFunctions), seenTypes(seenTypes),
                           collectAllFuns(collectAllFuns){}
  // this callback executes on a match
  void run(const clang::ast_matchers::MatchFinder::MatchResult &) override;
  
  // this callback executes at the end of the translation unit
  void onEndOfTranslationUnit() override{};
  private:
    FindFunctionMatcher subHandler;
    llvm::SetVector<FunctionInfo*> &seenFunctions;
    llvm::SetVector<const clang::Type*> &seenTypes;
    bool collectAllFuns;
};

// This visitor is used to recursively traverse types
// E.g. when a record is encountered, it will mark this record as seen, and
// recursively visit its fields and mark them as seen as well
class TypeCollectorVisitor
: public clang::RecursiveASTVisitor<TypeCollectorVisitor> {
public:
  explicit TypeCollectorVisitor(clang::ASTContext &Ctx,
                                llvm::SetVector<FunctionInfo*> &seenFunctions,
                                llvm::SetVector<const clang::Type*> &seenTypes)
                                : Ctx(Ctx), seenFunctions(seenFunctions), 
                                  seenTypes(seenTypes) {}
  bool VisitType(clang::Type *typ);
  // more concrete matchers can be added here if required
  // bool VisitRecordType(clang::RecordType *typ);
  // bool VisitPointerType(clang::PointerType *typ);
private:
  clang::ASTContext &Ctx;
  llvm::SetVector<FunctionInfo*> &seenFunctions;
  llvm::SetVector<const clang::Type*> &seenTypes;
};

class UsedFunAndTypeASTConsumer : public clang::ASTConsumer {
public:
  UsedFunAndTypeASTConsumer(llvm::SetVector<FunctionInfo*> &seenFunctions,
                            llvm::SetVector<const clang::Type*> &seenTypes,
                            bool collectAllFuns);
  void HandleTranslationUnit(clang::ASTContext &Ctx) override {
    finder.matchAST(Ctx);
  }
private:
  clang::ast_matchers::MatchFinder finder;
  FindEntryFunctionMatcher handler;
  llvm::SetVector<FunctionInfo*> &seenFunctions;
  llvm::SetVector<const clang::Type*> &seenTypes;
  bool collectAllFuns;
};

// collects all seen functions and types on construction
class UsedFunAndTypeCollector {
public:
  UsedFunAndTypeCollector(clang::ASTContext &Ctx,
                          bool collectAllFuns = false, // force collect funs
                          bool collectAllTypes = false) // force collect types
                          // todo: collectAllTypes actually only sets types as seen
  : collectAllTypes(collectAllTypes)
  {
    UsedFunAndTypeASTConsumer c(seenFunctions, seenTypes, 
                                collectAllFuns);
    c.HandleTranslationUnit(Ctx);
  }
  ~UsedFunAndTypeCollector();

  // returns function info if it Was seen, returns null otherwise
  FunctionInfo* getFunctionInfo (const clang::FunctionDecl* funDecl) const;

  bool functionIsSeen(const clang::FunctionDecl*);
  bool functionIsRecursive(const clang::FunctionDecl*);

  // checks if the passed type is in the list of seen types
  // the passed type must be canonical and should not contain any pointers
  bool typeIsSeen(const clang::Type*);
  bool typeIsSeen(const clang::QualType* t);

  llvm::SetVector<FunctionInfo*> getSeenFunctions() const {return seenFunctions;}
  llvm::SetVector<const clang::Type*> getSeenTypes() const {return seenTypes;}

private:
  llvm::SetVector<FunctionInfo*> seenFunctions;
  llvm::SetVector<const clang::Type*> seenTypes;
  bool collectAllTypes;
};
