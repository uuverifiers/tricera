#pragma once

#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/TypeVisitor.h"

// comments out the passed declaration using double slash comments
// todo: if there is another declaration in the same line, move it
bool doubleSlashCommentOutDeclaration (const clang::Decl* declaration, 
                                       clang::ASTContext &ctx,
                                       clang::Rewriter& rewriter);

// comments out the passed range with C-style comments (i.e. /*...*/)
// does not check if the range already contains C-style comments, which
// might lead to errors if they exist
// insertBeforeBegin and insertBefore end determine where the comments will
// be inserted w.r.t. the source beginning and end locations
void wrapWithCComment (clang::SourceRange sourceRange,
                       clang::Rewriter& rewriter,
                       bool insertBeforeBegin = true,
                       bool insertBeforeEnd = true);        

// This visitor is used to recursively traverse types
// and extract the underlying type free of pointers and qualifiers
class BaseTypeExtractor
: public clang::RecursiveASTVisitor<BaseTypeExtractor> {
public:
  explicit BaseTypeExtractor(clang::ASTContext &Ctx) : Ctx(Ctx) {}
  bool VisitType(clang::Type *typ);
  // more concrete matchers can be added here if required
  // bool VisitRecordType(clang::RecordType *typ);
  // bool VisitPointerType(clang::PointerType *typ);
  clang::Type* getExtractedType () const { return extractedType; }
private:
  clang::ASTContext &Ctx;
  clang::Type* extractedType;
};


// returns the previous declaration in the same statement if there exists one,
// returns nullptr otherwise.
// e.g. returns "int a" in "int a, b" if called with "int b"
const clang::Decl* getPrevDeclInSameStmt(const clang::Decl* decl);

// returns the next declaration in the same statement if there exists one,
// returns nullptr otherwise. the returned decl always have the same type
// as the passed decl, e.g. if TypedefDecl* decl, then a TypedefDecl* will
// be returned.
// e.g. returns "int b" in "int a, b" if called with "int a"
const clang::Decl* getNextDeclInSameStmt(const clang::Decl* decl);
