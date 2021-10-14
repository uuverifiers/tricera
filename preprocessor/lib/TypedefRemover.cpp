#include "TypedefRemover.hpp"
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

TypedefRemoverASTConsumer::TypedefRemoverASTConsumer(clang::Rewriter &r,
                                   UsedFunAndTypeCollector & usedFunsAndTypes):
                                    handler(r, usedFunsAndTypes), rewriter(r) {
  DeclarationMatcher typedefDeclMatcher = anyOf(
    typedefDecl( // matches typedef records
      anyOf(
        allOf( // that are elaborated
          hasType(elaboratedType().bind("anElabType")),
          hasDescendant(recordType().bind("aTypedefRecord"))
        ), // or not
        hasDescendant(recordType().bind("aTypedefRecord")),
        allOf( // that are elaborated
          hasType(elaboratedType().bind("anElabType")),
          hasDescendant(enumType().bind("aTypedefEnum"))
        ), // or not
        hasDescendant(enumType().bind("aTypedefEnum"))
      )
    ).bind("aTypedefDecl"),
    typedefDecl( // matches all other typedefs
      unless(hasDescendant(recordType()))).bind("aTypedefDecl")
  );
  finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource, typedefDeclMatcher), &handler);
}

void TypedefMatcher::run(const MatchFinder::MatchResult &Result) {
  // ASTContext is used to retrieve the source location
  ASTContext *Ctx = Result.Context;

  // this callback removes all typedef declarations,
  // record typedefs which also has a record body are converted to regular
  // record declarations if they are in UsedFunctionAndTypeCollector::seenTypes

  const TypedefDecl * TheTypedefDecl =
    Result.Nodes.getNodeAs<clang::TypedefDecl>("aTypedefDecl");

  if (!TheTypedefDecl)
    assert(false && "Typedef remover handler called but could not determine match!\n");

  // remove all typedef declarations from source code
  //TheTypedefDecl->dump();
  SourceLocation TypeDefBeginLoc;
  SourceLocation TypeDefEndLoc;
  const Decl* prevDecl = TheTypedefDecl->getPreviousDecl();
  if(prevDecl && prevDecl->getEndLoc().isValid()) { // there is a previous declaration
    TypeDefBeginLoc = prevDecl->getEndLoc().getLocWithOffset(1);
  } else { // there is no previous declaration
    TypeDefBeginLoc = TheTypedefDecl->getBeginLoc();
  }

  // return if this declaration is not in the main file
  if (Ctx->getFullLoc(TypeDefBeginLoc).getFileID() !=
       rewriter.getSourceMgr().getMainFileID()) return;

  // get end location of typedef, this might correspond to the end location of
  // the last declaration for this typedef, e.g. typedef struct T {} T1, T2...;
  const TypedefDecl * curDecl = TheTypedefDecl;
  const TypedefDecl * lastDecl;
  while(curDecl) {
    lastDecl = curDecl;
    curDecl = static_cast<const TypedefDecl*>(getNextDeclInSameStmt(curDecl));
    assert(curDecl != lastDecl);
  }

  TypeDefEndLoc = Lexer::findLocationAfterToken(lastDecl->getEndLoc(),
    tok::semi, Ctx->getSourceManager(), Ctx->getLangOpts(), false);
  if (!TypeDefEndLoc.isValid())
    TypeDefEndLoc = lastDecl->getEndLoc();

  if(!TypeDefBeginLoc.isValid() || !TypeDefEndLoc.isValid()) return;
   // this is to prevent deleting/commenting multiple typedefs.
   // e.g.: typedef struct S {...} S1, S2;
  if (!EditedLocations.insert(TypeDefBeginLoc).second){
    //llvm::outs() << "already edited!\n";
    return;
  }

  // check if the type this typedef is referring to was never seen.
  // if so, the whole declaration will be commented out
  BaseTypeExtractor typeVisitor(*Ctx);
  typeVisitor.TraverseType(Ctx->getTypedefType(TheTypedefDecl).getCanonicalType());
  const clang::Type* baseType = typeVisitor.getExtractedType();

  bool typeSeen = usedFunsAndTypes.typeIsSeen(baseType);

  if (!typeSeen) {
    //llvm::outs() << "this type was never seen\n";
    //TheTypedefDecl->dump();
    ///baseType->dump();
  }

  // check if this typedef contains a record (struct/union) declaration
  const RecordType * TheRecordType =
    Result.Nodes.getNodeAs<clang::RecordType>("aTypedefRecord");
  const EnumType * TheEnumType =
    Result.Nodes.getNodeAs<clang::EnumType>("aTypedefEnum");

  bool declaresRecord = false;
  FullSourceLoc RecordDeclBeginLoc;
  FullSourceLoc RecordDeclEndLoc;
  if(TheRecordType || TheEnumType) {
    Decl* recOrEnumDecl;
    if (TheRecordType) recOrEnumDecl = TheRecordType->getDecl();
    else if (TheEnumType) recOrEnumDecl = TheEnumType->getDecl();
    else llvm_unreachable("");
    //RecordDecl* TheRecordDecl = TheRecordType->getDecl();
    //EnumDecl* TheEnumDecl = TheEnumType->getDecl();
    // get the beginning of the record declaration
    RecordDeclBeginLoc = Ctx->getFullLoc(recOrEnumDecl->getBeginLoc());
    // get the end of the record declaration
    RecordDeclEndLoc   = Ctx->getFullLoc(recOrEnumDecl->getEndLoc());
    if(RecordDeclBeginLoc >= TypeDefBeginLoc &&
       RecordDeclEndLoc <= TypeDefEndLoc)
       declaresRecord = true;
  }

  if (declaresRecord && typeSeen) {
    //const RecordDecl * TheRecordDecl = TheRecordType->getAsRecordDecl();
    std::string declName;
    if (TheRecordType) declName = TheRecordType->getDecl()->getNameAsString();
    else if (TheEnumType) declName = TheEnumType->getDecl()->getNameAsString();
    else llvm_unreachable("");
    // comment out / remove the typedef keyword and
    // end the comment right before record declaration starts
    wrapWithCComment(SourceRange(TypeDefBeginLoc, RecordDeclBeginLoc),
                     rewriter);

    // comment out / remove the typedef names right after the record
    // end the comment right before the semicolon
    wrapWithCComment(SourceRange(
      RecordDeclEndLoc, TypeDefEndLoc.getLocWithOffset(-1)),
                     rewriter, false);

    // copies x in "typedef struct {} x" to right after "struct" if missing
    if(declName.empty())
      rewriter.InsertTextAfterToken(RecordDeclBeginLoc,
        (" " + TheTypedefDecl->getNameAsString()));
  } else { // if typedef does not contain a record declaration
    // comment it out (or alternatively remove it)
    //llvm::outs()<<"commenting out decl\n";
    //lastDecl->dump();
    doubleSlashCommentOutDeclaration(lastDecl, *Ctx, rewriter);

    //rewriter.InsertTextBefore(TypeDefBeginLoc, "/* ");
    //rewriter.InsertTextAfterToken(TypeDefEndLoc, " */");
    //rewriter.RemoveText(SourceRange(TypeDefBeginLoc,TypeDefEndLoc.getLocWithOffset(-1)));
  }
}
