#include "UsedFunctionAndTypeCollector.hpp"

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

// any functions in this list will not be marked as used, and in turn will be
// commented out later by the preprocessor (if UnusedDeclCommenter is used)
static const std::vector<std::string> ignoredFuns = {
    "__assert_fail", "__assert_perror_fail", "__assert", "reach_error", 
    "__VERIFIER_error", "static_assert", "assert", "assume", "malloc",
    "__VERIFIER_assume", "calloc", "realloc", "free", "abort", "exit",
    "memset", "memcmp"};

// todo: add another handler to only collect types
void handleFunDecl(const clang::FunctionDecl* funDecl,
                   clang::ast_matchers::MatchFinder::MatchCallback* handler,
                   clang::ASTContext *Ctx) {

  //std::string funName = funDecl->getNameAsString();
  //if (std::find(ignoredFuns.begin(), ignoredFuns.end(), funName) != 
  //  ignoredFuns.end())
  //  return;
  
  StatementMatcher CallSiteOrDeclRefMatcher = anyOf(
  callExpr(
    hasAncestor(functionDecl(hasName(funDecl->getName())).bind("enclosing")),
    callee(functionDecl().bind("callee"))).bind("caller"),
  declRefExpr(allOf(hasAncestor(functionDecl(hasName(funDecl->getName())).bind("enclosing")),
    unless(anyOf(hasType(functionProtoType()),
      hasType(functionType()),
      hasType(builtinType()))),
    anyOf(hasType(typedefType().bind("typedefTyp")),
      hasType(arrayType().bind("arrayTyp")),
      hasType(recordType().bind("recordTyp")),
      anything()))
  ).bind("referenceExpr"));
  
  TypeLocMatcher usedTypesMatcher = typeLoc(
    loc(qualType().bind("usedType")), 
    hasAncestor(expr()), // this ensures that the type is used in an expr.
    hasAncestor(functionDecl(hasName(funDecl->getName())))).bind("usedTypeLoc");

  clang::ast_matchers::MatchFinder finder;
  finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource, CallSiteOrDeclRefMatcher), handler);
  finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource, usedTypesMatcher), handler);
  finder.matchAST(*Ctx);
}

// this is the first consumer for the AST, it only finds the entry point,
// and creates sub-consumers (UsedFunAndTypeASTConsumerHelper) to find
// called functions and used types
UsedFunAndTypeASTConsumer::UsedFunAndTypeASTConsumer (
  llvm::SetVector<FunctionInfo*> &seenFunctions,
  llvm::SetVector<const clang::Type*> &seenTypes, bool collectAllFuns) : 
  seenFunctions(seenFunctions), seenTypes(seenTypes), 
  handler(seenFunctions, seenTypes, collectAllFuns) {

  if (collectAllFuns) {
    DeclarationMatcher entryMatcher = anyOf(
      functionDecl(hasDescendant(callExpr(callee(functionDecl( // a recursive fun
        equalsBoundNode("allFunDecl")))).bind("recCall"))).bind("allFunDecl"),
      functionDecl().bind("allFunDecl")); // a non-recursive fun
    finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource, entryMatcher), &handler);
  } else {
    DeclarationMatcher entryMatcher = functionDecl(isMain()).bind("main");
    // todo: other entry points than main
    finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource, entryMatcher), &handler);
  }
}

// This is the handler that is called when the entry function is found
void FindEntryFunctionMatcher::run(const MatchFinder::MatchResult &Result) {
  clang::ASTContext *Ctx = Result.Context;

  const clang::FunctionDecl * entryFunction =
    Result.Nodes.getNodeAs<clang::FunctionDecl>("main"); 
  
  const clang::FunctionDecl * allFunDecl =
    Result.Nodes.getNodeAs<clang::FunctionDecl>("allFunDecl"); 

  if (entryFunction) {
    //llvm::outs() << "main found...\n";
    seenFunctions.insert(new FunctionInfo(entryFunction, false)); // todo: add main args as seen types
    handleFunDecl(entryFunction, &subHandler, Ctx);
  } else if (allFunDecl) {
    const clang::CallExpr * recCall = 
      Result.Nodes.getNodeAs<clang::CallExpr>("allFunDecl");
    seenFunctions.insert(new FunctionInfo(allFunDecl, recCall != nullptr));
    handleFunDecl(allFunDecl, &subHandler, Ctx); 
    // todo: another handler which only collects types would be more efficient above
  }else {
    // if entryFunction is null, the entry point could not be found
    llvm_unreachable("main function could not be found.");
  }
}

void FindFunctionMatcher::run(const MatchFinder::MatchResult &Result) {
  // ASTContext is used to retrieve the source locations
  ASTContext *Ctx = Result.Context;

  const FunctionDecl * CalleeDecl =
      Result.Nodes.getNodeAs<clang::FunctionDecl>("callee");
  const FunctionDecl * EnclosingDecl =
      Result.Nodes.getNodeAs<clang::FunctionDecl>("enclosing");
  const CallExpr * TheCall = Result.Nodes.getNodeAs<clang::CallExpr>("caller");
  
  //llvm::outs() << CalleeDecl->getNameAsString() << " called from " << 
  //  EnclosingDecl->getNameAsString() << "\n";

  const TypeLoc * usedTypeLoc = Result.Nodes.getNodeAs<clang::TypeLoc>("usedTypeLoc");
  
  const DeclRefExpr * TheRef = Result.Nodes.getNodeAs<clang::DeclRefExpr>("referenceExpr");
  if(TheRef) { // matched a DeclRefExpr                              
    //llvm::outs() << "matched a ref\n";
    //TheRef->dump();
    QualType typ = TheRef->getType();
    //bool hasBuiltinType = typ->isBuiltinType();

    //if (!hasBuiltinType) {
      TypeCollectorVisitor typeVisitor(*Ctx, seenFunctions, seenTypes);
      typeVisitor.TraverseType(typ);
    //}
  } else if (CalleeDecl) { // matched a CallExpr
    //llvm::outs() << EnclosingDecl->getNameAsString() << "\n";
   
    assert(declaresSameEntity(TheCall->getDirectCallee(), CalleeDecl));

    // todo: maybe detect mutually recursive funs, or recursion afterseveral steps
    bool functionIsRecursive = declaresSameEntity(CalleeDecl, EnclosingDecl);
    
    bool functionSeenBefore = false;
    if (std::find(ignoredFuns.begin(), ignoredFuns.end(), 
        CalleeDecl->getNameAsString()) != ignoredFuns.end())
      functionSeenBefore = true;
    else
      for(int i = 0; i < seenFunctions.size(); ++i){
        if(declaresSameEntity(seenFunctions[i]->getDecl(), CalleeDecl)){
          functionSeenBefore = true;
          if(!seenFunctions[i]->isRecursive() && functionIsRecursive)
            seenFunctions[i]->setRecursive();
          break;
        }
      }
    //if(functionIsRecursive)
    //    llvm::outs() << "  " << CalleeDecl->getNameAsString() << " is recursive!\n";

    if (!functionSeenBefore) {
      //llvm::outs() << "seeing " << CalleeDecl->getNameAsString() << " for the first time!\n";
      
      // try to find a declaration with a body, if one exists
      const FunctionDecl * calleeWithBody = CalleeDecl;
      for (auto decl : CalleeDecl->redecls()) {
        if (decl->hasBody())
          calleeWithBody = decl;
      }
      seenFunctions.insert(new FunctionInfo(calleeWithBody, functionIsRecursive)); // callee not seen before

      // mark the return and argument types of this function as seen
      TypeCollectorVisitor typeVisitor(*Ctx, seenFunctions, seenTypes);
      typeVisitor.TraverseType(CalleeDecl->getReturnType());
      for (auto paramDecl : CalleeDecl->parameters())
        typeVisitor.TraverseType(paramDecl->getType());

      //llvm::outs() << "  " << CalleeDecl->getNameAsString() << " called from " << 
      //  EnclosingDecl->getNameAsString() << "\n";
      
      handleFunDecl(calleeWithBody, this, Ctx);
    }
  } else if (usedTypeLoc) {
      const clang::QualType* usedType =  Result.Nodes.getNodeAs<clang::QualType>("usedType");
    //if (!usedType->getTypePtr()->isBuiltinType()) {
      //llvm::outs() << "seen type\n";
      //usedType->dump();
      TypeCollectorVisitor typeVisitor(*Ctx, seenFunctions, seenTypes);
      typeVisitor.TraverseType(*usedType);
    //}
  } else {
    llvm_unreachable("Handler without any matches should not be possible...");
  }
}

bool TypeCollectorVisitor::VisitType(clang::Type *typ) {
  //typ->dump();
  const clang::Type* canonicalType = typ->getCanonicalTypeUnqualified().getTypePtr();
  if (/*!canonicalType->isBuiltinType() && */!canonicalType->isPointerType()) {
    bool res = seenTypes.insert(typ->getCanonicalTypeUnqualified().getTypePtr());
    if (res) {
      //llvm::outs() << "inserted unseen type: \n";
      //typ->getCanonicalTypeUnqualified().dump();
      if (typ->isRecordType()) {
        //llvm::outs() << "this is a record type, checking fields...\n";
        RecordDecl* recordDecl = typ->getAsRecordDecl();
        //recordDecl->dump();
        TypeCollectorVisitor typeVisitor(Ctx, seenFunctions, seenTypes);
        for (auto field : recordDecl->fields()) {
          //llvm::outs() << "field: \n";
          //field->dump();
          typeVisitor.TraverseType(field->getType());
        }
      }
    }
  } else if (canonicalType->isPointerType()) {
    //llvm::outs() << "pointer type\n";
    TypeCollectorVisitor typeVisitor(Ctx, seenFunctions, seenTypes);
    typeVisitor.TraverseType(canonicalType->getPointeeType());
  } /*else {
    llvm::outs() << "builtin type\n";
    llvm::outs() << "------------------------------------------------\n";
    return false;
  }*/
  return true;
}

FunctionInfo* UsedFunAndTypeCollector::getFunctionInfo (
  const clang::FunctionDecl* funDecl) const {
  for (auto funInfo : seenFunctions)
    if (declaresSameEntity(funDecl, funInfo->getDecl()))
      return funInfo;
  return nullptr;
}

bool UsedFunAndTypeCollector::functionIsSeen(
  const clang::FunctionDecl* funDecl) {
  return getFunctionInfo(funDecl) != nullptr;
}

bool UsedFunAndTypeCollector::functionIsRecursive(
  const clang::FunctionDecl* funDecl) {
  const FunctionInfo* funInfo = getFunctionInfo(funDecl);
  if (funInfo)
    return funInfo->isRecursive();
  else 
    llvm_unreachable("Tried to check if unsee function is recursive!");
}

bool UsedFunAndTypeCollector::typeIsSeen(const clang::Type* t) {
  if (collectAllTypes) return true;
  for (auto typ : seenTypes)
    if (typ == t)
      return true;
  return false;
}

bool UsedFunAndTypeCollector::typeIsSeen(const clang::QualType* t) {
  return typeIsSeen(t->getTypePtr());
}

UsedFunAndTypeCollector::~UsedFunAndTypeCollector() {
  // cleanup
  for (int i = 0; i < seenFunctions.size(); ++i)
    delete seenFunctions[i];
}
