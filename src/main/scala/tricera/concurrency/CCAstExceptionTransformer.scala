/**
 * Copyright (c) 2026 Hugo Sacilotto. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package tricera.concurrency

import concurrent_c._
import concurrent_c.Absyn._

import scala.collection.mutable.{HashMap => MHashMap, ListBuffer}
import scala.collection.mutable.Set
import scala.collection.mutable.Stack
import scala.jdk.CollectionConverters._

class ExceptionTransformException(msg : String) extends Exception(msg)

object CCAstExceptionTransformer {
  type FuncExceptionTypeData = Set[ListBuffer[Type_specifier]]

  private val exceptionFlagVarName = "__exception_flag"
  private val exceptionTypeVarName = "__exception_type"
  private val exceptionValueVarName = "__exception_value"
  private val exceptionValueStructName = "ExceptionValue"
  private val exceptionTypeEnumName = "ExceptionType"

  private val getName = new CCAstGetNameVistor
  private var counter = 0

  private def getId(): Int = {
    counter += 1
    counter
  }

  private def typeSpecToString(typeSpec: Type_specifier): String = {
    typeSpec match {
      case t: Tvoid => "void"
      case t: Tbool => "_Bool"
      case t: Tchar => "char"
      case t: Tshort => "short"
      case t: Tint => "int"
      case t: Tlong => "long"
      case t: Tsigned => "signed"
      case t: Tunsigned => "unsigned"
      case t: Tstruct => t.struct_or_union_spec_ match {
        case tagType: TagType => "struct" + "_" + tagType.cident_
        case _ => throw new ExceptionTransformException("Invalid parameter declaration in catch")
      }
      case t: Tenum => t.enum_specifier_ match {
        case enumVar: EnumVar => "enum" + "_" + enumVar.cident_
        case _ => throw new ExceptionTransformException("Invalid parameter declaration in catch")
      }
      case _ => throw new ExceptionTransformException("Not supported type")
    }
  }

  private def typeLabelName(listDecSpec: ListDeclaration_specifier): String = {
    val str = new StringBuilder
    var joiner = ""
    for (decSpec <- listDecSpec.asScala) {
      str.append(joiner)
      joiner = "_"
      str.append(decSpec match {
        case _type: Type => typeSpecToString(_type.type_specifier_)
        case _ => ""
      })
    }
    str.toString()
  }

  private def typeLabelName(types: ListBuffer[Type_specifier]): String = {
    val str = new StringBuilder
    var joiner = ""
    for (type_ <- types) {
      str.append(joiner)
      joiner = "_"
      str.append(typeSpecToString(type_))
    }
    str.toString()
  }

  private def typeLabelName(paramDecl: Parameter_declaration): String = {
    paramDecl match {
      case t: OnlyType => typeLabelName(t.listdeclaration_specifier_)
      case t: TypeAndParam => typeLabelName(t.listdeclaration_specifier_)
      case _ => throw new ExceptionTransformException("Invalid type as parameter declaration")
    }
  }

  private def createExceptionTypeEnumName(typeSpecList: ListBuffer[Type_specifier]): String = {
    typeLabelName(typeSpecList).toUpperCase()
  }

  private def createExceptionStructField(typeSpecList: ListBuffer[Type_specifier]): String = {
    typeLabelName(typeSpecList) + "_v"
  }

  private def createExceptionStructField(listDecSpec: ListDeclaration_specifier): String = {
    typeLabelName(listDecSpec) + "_v"
  }

  private def catchBlockLabelName(funcName: String, paramDecl: Parameter_declaration, catchId: Int): String = {
    paramDecl match {
      case catchAll: More => funcName + "_catch_all_" + catchId.toString()
      case typeAndParam: TypeAndParam =>
        funcName + "_catch_" + 
        typeLabelName(typeAndParam.listdeclaration_specifier_) + "_" +
        typeAndParam.declarator_.accept(getName, ()) + "_" + catchId.toString()
      case onlyType: OnlyType => 
        funcName + "_catch_" +
        typeLabelName(onlyType.listdeclaration_specifier_) + "_" + catchId.toString()
      case _ => throw new ExceptionTransformException("Invalid parameter declaration in catch")
    }
  }

  private def afterCatchLabelName(funcName: String, catchId: Int): String = {
    funcName + "_after_catch_" + catchId.toString()
  }

  private def declarationAssignmentStm(t: ListDeclaration_specifier, varName: String, exp: Exp): Stm = {
    val listInitDecl = new ListInit_declarator
    listInitDecl.add(new InitDecl(new NoPointer(new Name(varName)), new InitExpr(exp)))
    new DecS(new Declarators(t, listInitDecl, new ListExtra_specifier))
  }

  private case class ExceptionTypesCollectionResult(
    funcExceptionTypes: Map[String, FuncExceptionTypeData],
    exceptionTypes: Set[ListBuffer[Type_specifier]]
  )

  def transform(program: Program): Program = {
    val collectionResult = collectExceptionTypes(program)
    val funcReturnTypes = collectFuncReturnTypes(program)
    val transformer = new ExceptionTransformer(collectionResult, funcReturnTypes)
    val transformedProgram = program.accept(transformer, null)
    transformedProgram
  }

  private def collectExceptionTypes(program: Program): ExceptionTypesCollectionResult = {
    val funcExceptionTypesMap = new MHashMap[String, FuncExceptionTypeData]
    program.accept(new FuncExceptionTypesCollector(funcExceptionTypesMap), null)

    val exceptionTypes = Set[ListBuffer[Type_specifier]]()
    program.accept(new ExceptionTypesCollector(exceptionTypes), null)

    // Add all exception types to every function
    // This can be removed if function exception types are collected properly.
    funcExceptionTypesMap.keys.foreach(funcName => funcExceptionTypesMap.put(funcName, exceptionTypes))

    ExceptionTypesCollectionResult(funcExceptionTypesMap.toMap, exceptionTypes)
  }

  private def collectFuncReturnTypes(program: Program): MHashMap[String, ListDeclaration_specifier] = {
    val funcReturnTypesMap = new MHashMap[String, ListDeclaration_specifier]
    program.accept(new FuncReturnTypesCollector(funcReturnTypesMap), null)
    funcReturnTypesMap
  }

  private def typeOfThrownExp(thrownExp: Exp): ListBuffer[Type_specifier] = {
    // The TriCera preprocessor adds a cast as a type hint for thrown expressions
    thrownExp match {
      case e: Etypeconv => typeNameToListOfTypeSpec(e.type_name_)
      case _ => throw new ExceptionTransformException("Missing cast in thrown expression")
    }
  }

  private def typeNameToListOfTypeSpec(typeName: Type_name): ListBuffer[Type_specifier] = {
    val types = new ListBuffer[Type_specifier]
    typeName match {
      case plain: PlainType => plain.listspec_qual_.asScala.foreach(spec_qual => {
        spec_qual match {
          case typeSpec: TypeSpec => {
            types.addOne(typeSpec.type_specifier_)
          }
          case _ => throw new ExceptionTransformException("Invalid type declaration")
        }
      })
      case _ => throw new ExceptionTransformException("Invalid type declaration")
    }

    types
  }

  private def listDeclSpecToListOfTypeSpec(listDeclSpec: ListDeclaration_specifier): ListBuffer[Type_specifier] = {
    val types = new ListBuffer[Type_specifier]
    listDeclSpec.asScala.foreach(decl => {
      decl match {
        case t: Type => {
          types.addOne(t.type_specifier_)
        }
        case _ => throw new ExceptionTransformException("Invalid type declaration")
      }
    })
    types
  }

  private class ExceptionTypesCollector(
    val exceptionTypesBuffer: Set[ListBuffer[Type_specifier]]
  ) extends ComposVisitor[Any] {
    override def visit(throwExp: EthrowOne, arg: Any): EthrowOne = {
      val thrownType = typeOfThrownExp(throwExp.exp_)
      exceptionTypesBuffer.add(thrownType)
      throwExp
    }

    override def visit(catchStm: Scatch, arg: Any): Catch_stm = {
      val paramDecl = catchStm.parameter_declaration_
      val block = catchStm.compound_stm_
      val typeSpecList = new ListBuffer[Type_specifier]

      paramDecl match {
        case onlyType: OnlyType => {
          for (declSpec <- onlyType.listdeclaration_specifier_.asScala) {
            declSpec match {
              case t: Type => {
                typeSpecList.addOne(t.type_specifier_)
              }
            }
          }
        }
        case typeAndParam: TypeAndParam => {
          for (declSpec <- typeAndParam.listdeclaration_specifier_.asScala) {
            declSpec match {
              case t: Type => {
                typeSpecList.addOne(t.type_specifier_)
              }
            }
          }
        }
        case _ => {}
      }

      if (!typeSpecList.isEmpty) {
        exceptionTypesBuffer.add(typeSpecList)
      }

      block.accept(this, arg)
      catchStm
    }
  }

  /**
   * Naive approach to collecting exception types for functions 
   * that may throw. Only considers throw statements in function
   * definitions and not function calls.
   */
  private class FuncExceptionTypesCollector(
    val funcExceptionTypesBuffer: MHashMap[String, FuncExceptionTypeData]
  ) extends ComposVisitor[FuncExceptionTypeData] {
    override def visit(func: NewFunc, arg: FuncExceptionTypeData): NewFunc = {
      val blockStm = func.compound_stm_
      val funcExceptionTypeData = Set[ListBuffer[Type_specifier]]()

      blockStm.accept(this, funcExceptionTypeData)
      val funcName = func.accept(getName, ())
      funcExceptionTypesBuffer.put(funcName, funcExceptionTypeData)

      func
    }

    override def visit(func: AnnotatedFunc, arg: FuncExceptionTypeData): AnnotatedFunc = {
      val blockStm = func.compound_stm_
      val funcExceptionTypeData = Set[ListBuffer[Type_specifier]]()

      blockStm.accept(this, funcExceptionTypeData)
      val funcName = func.accept(getName, ())
      funcExceptionTypesBuffer.put(funcName, funcExceptionTypeData)

      func
    }

    override def visit(throwExp: EthrowOne, arg: FuncExceptionTypeData): EthrowOne = {
      val thrownType = typeOfThrownExp(throwExp.exp_)
      arg.addOne(thrownType)
      throwExp
    }
  }

  private class FuncReturnTypesCollector(
    val funcTypesBuffer: MHashMap[String, ListDeclaration_specifier]
  ) extends ComposVisitor[ListDeclaration_specifier] {
    override def visit(func: NewFunc, arg: ListDeclaration_specifier): NewFunc = {
      val listDecSpec = func.listdeclaration_specifier_
      val funcName = func.accept(getName, ())
      funcTypesBuffer.put(funcName, listDecSpec)

      func
    }

    override def visit(func: AnnotatedFunc, arg: ListDeclaration_specifier): AnnotatedFunc = {
      val listDecSpec = func.listdeclaration_specifier_
      val funcName = func.accept(getName, ())
      funcTypesBuffer.put(funcName, listDecSpec)

      func
    }  
  }

  private class ExceptionTransformer(
    val exceptionTypeData: ExceptionTypesCollectionResult,
    val funcReturnTypesMap: MHashMap[String, ListDeclaration_specifier],
  ) extends ComposVisitor[(String, Stack[ListBuffer[(Parameter_declaration, Int)]], Option[Parameter_declaration])] with CopyAstLocation {
    private val getName = new CCAstGetNameVistor
    private val funcExceptionTypeData = exceptionTypeData.funcExceptionTypes
    private val exceptionTypes = exceptionTypeData.exceptionTypes

    private val setExceptionFlag = new ExprS(
      new SexprTwo(
        new Eassign(
          new Evar(exceptionFlagVarName),
          new Assign,
          new Econst(new Eint("1"))
        )
      )
    )
    private val unsetExceptionFlag = new ExprS(
      new SexprTwo(
        new Eassign(
          new Evar(exceptionFlagVarName),
          new Assign,
          new Econst(new Eint("0"))
        )
      )
    )

    private val emptyReturnStm = new JumpS(new SjumpFour)
    private val abortStm = new ExprS(new SexprTwo(new Efunk(new Evar("abort"))))

    private def returnStm(e: Exp): Stm = {
      new JumpS(new SjumpFive(e))
    }

    private def globalVarDecl(typeSpecList: List[Type_specifier], varName: String, optE: Option[Exp]): Global = {
      val declSpec = new ListDeclaration_specifier
      typeSpecList.foreach(typeSpec => declSpec.add(new Type(typeSpec)))

      val initDecls = new ListInit_declarator
      optE match {
        case Some(e) => initDecls.add(new InitDecl(new NoPointer(new Name(varName)), new InitExpr(e)))
        case None => initDecls.add(new OnlyDecl(new NoPointer(new Name(varName))))
      }
      new Global(new Declarators(declSpec, initDecls, new ListExtra_specifier))
    }

    private def globalStructDecl(structName: String, fields: List[(List[Type_specifier], String)]): Global = {
      val declSpecList = new ListDeclaration_specifier
      val structDecs = new ListStruct_dec

      for ((typeSpecList, fieldName) <- fields) {
        val specQualList = new ListSpec_qual
        typeSpecList.foreach(typeSpec => specQualList.add(new TypeSpec(typeSpec)))

        val structDeclaratorList = new ListStruct_declarator
        structDeclaratorList.add(new Decl(new NoPointer(new Name(fieldName))))
        structDecs.add(new Structen(specQualList, structDeclaratorList))
      }

      declSpecList.add(new Type(new Tstruct(new Tag(new Struct, structName, structDecs))))
      new Global(new NoDeclarator(declSpecList, new ListExtra_specifier))
    }

    private def globalEnumDecl(enumName: String, variants: List[String]): Global = {
      val enumeratorList = new ListEnumerator
      variants.foreach(variant => enumeratorList.add(new Plain(variant)))

      val declSpecList = new ListDeclaration_specifier
      declSpecList.add(new Type(new Tenum(new EnumName(enumName, enumeratorList))))
      new Global(new NoDeclarator(declSpecList, new ListExtra_specifier))
    }

    private def paramDeclToTypeSpecList(paramDecl: Parameter_declaration): ListBuffer[Type_specifier] = {
      paramDecl match {
        case p: More => throw new ExceptionTransformException("Unable to convert '...' declaration to list of type specifiers")
        case p: OnlyType => listDeclSpecToListOfTypeSpec(p.listdeclaration_specifier_)
        case p: TypeAndParam => listDeclSpecToListOfTypeSpec(p.listdeclaration_specifier_)
        case p: TypeHintAndParam => listDeclSpecToListOfTypeSpec(p.listdeclaration_specifier_)
        case p: Abstract => listDeclSpecToListOfTypeSpec(p.listdeclaration_specifier_)
      }
    }

    override def visit(
      p: Progr,
      arg: (String, Stack[ListBuffer[(Parameter_declaration, Int)]], Option[Parameter_declaration])
    ): Program = {
      val originalProgDecls = p.listexternal_declaration_
      val extDeclarations = new ListExternal_declaration

      // Not type or variable declarations
      // They are added last
      val otherDeclarations = new ListExternal_declaration

      for (dec <- originalProgDecls.asScala) {
        dec match {
          case g: Global => {
            extDeclarations.add(g.accept(this, arg))
          }
          case d => {
            otherDeclarations.add(d.accept(this, arg))
          }
        }
      }

      // Enum declaration for exception types
      extDeclarations.add(
        globalEnumDecl(
          exceptionTypeEnumName, 
          exceptionTypes.map(t => createExceptionTypeEnumName(t)).toList
        )
      )

      // Struct declaration for exception values
      extDeclarations.add(
        globalStructDecl(
          exceptionValueStructName, 
          exceptionTypes.map(t => (t.toList, createExceptionStructField(t))).toList
        )
      )

      // Global variables for exception information
      extDeclarations.add(
        globalVarDecl(
          List(new Tint()), exceptionFlagVarName, None
        )
      )
      extDeclarations.add(
        globalVarDecl(
          List(new Tenum(new EnumVar(exceptionTypeEnumName))),
          exceptionTypeVarName,
          None
        )
      )
      extDeclarations.add(
        globalVarDecl(
          List(new Tstruct(new TagType(new Struct, exceptionValueStructName))),
          exceptionValueVarName,
          None
        )
      )

      otherDeclarations.asScala.foreach(d => extDeclarations.add(d))

      super.visit(p, arg)
      copyLocationInformation(p, new Progr(extDeclarations))
    }

    private def setExceptionType(typeSpecList: ListBuffer[Type_specifier]): ExprS = {
      new ExprS(
        new SexprTwo(
          new Eassign(
            new Evar(exceptionTypeVarName),
            new Assign,
            new Evar(createExceptionTypeEnumName(typeSpecList))
          )
        )
      )
    }

    private def setExceptionValue(typeSpecList: ListBuffer[Type_specifier], exp: Exp): ExprS = {
      new ExprS(
        new SexprTwo(
          new Eassign(
            new Eselect(
              new Evar(exceptionValueVarName),
              createExceptionStructField(typeSpecList)
            ),
            new Assign, exp
          )
        )
      )
    }

    private def gotoStm(labelName: String): JumpS = {
      new JumpS(new SjumpOne(labelName))
    }

    private def emptyLabelStm(labelName: String): LabelS = {
      new LabelS(new SlabelOne(labelName, new ExprS(new SexprOne)))
    }

    private def ifStm(exp: Exp, stm: Stm, optStm: Option[Stm]): Selection_stm = {
      optStm match {
        case None => new SselOne(exp, stm)
        case Some(elseStm) => new SselTwo(exp, stm, elseStm)
      }
    }

    private def switchExceptionTypeCatch(cases: ListBuffer[(ListBuffer[Type_specifier], Stm)]): Selection_stm = {
      val stmList = new ListStm

      for ((typeSpec, stm) <- cases) {
        stmList.add(
          new LabelS(new SlabelTwo(new Especial(new Evar(createExceptionTypeEnumName(typeSpec))), stm))
        )
      }

      new SselThree(
        new Evar(exceptionTypeVarName),
        new CompS(new ScompTwo(stmList))
      )
    }

    override def visit(
      funcDef: Afunc,
      arg: (String, Stack[ListBuffer[(Parameter_declaration, Int)]], Option[Parameter_declaration])
    ): External_declaration = {
      val funcName = funcDef.accept(getName, ())
      copyLocationInformation(
        funcDef,
        new Afunc(
          funcDef.function_def_.accept(
            this,
            (funcName, new Stack[ListBuffer[(Parameter_declaration, Int)]], None)
          )
        )
      )
    }

    /**
     * Function to find the first handler able to catch the thrown exception.
     * Returns the label name of the corresponding handler, and None if no
     * such handler exists.
     */
    private def findMatchingCatch(
      funcName: String,
      thrownType: ListBuffer[Type_specifier],
      catchStack: Stack[(ListBuffer[(Parameter_declaration, Int)])],
    ): Option[String] = {
        val catchStackCopy = catchStack.clone()

        while (!catchStackCopy.isEmpty) {
          val catchTypes = catchStackCopy.pop()
          val iter = catchTypes.iterator

          // Check the handlers in order for a matching type
          while (iter.hasNext) {
            val (catchType, catchId) = iter.next
            catchType match {
              case catchAll: More => {
                return Some(catchBlockLabelName(funcName, catchType, catchId))
              }
              case typeAndParam: TypeAndParam => {
                // Compare type of expression to catch handler's type
                if (listDeclSpecToListOfTypeSpec(typeAndParam.listdeclaration_specifier_) == thrownType) {
                  return Some(catchBlockLabelName(funcName, catchType, catchId))
                }
              }
              case onlyType: OnlyType => {
                if (listDeclSpecToListOfTypeSpec(onlyType.listdeclaration_specifier_) == thrownType) {
                  return Some(catchBlockLabelName(funcName, catchType, catchId))
                }
              }
              case _ => throw new ExceptionTransformException("Invalid type declaration in catch")
            }
          }
        }

        None
    }

    private def switchExceptionCases(
      outerFuncName: String,
      catchStack: Stack[ListBuffer[(Parameter_declaration, Int)]],
      types: Set[ListBuffer[Type_specifier]]
    ): ListBuffer[(ListBuffer[Type_specifier], Stm)] = {
      val cases = new ListBuffer[(ListBuffer[Type_specifier], Stm)]

      // For every possible exception type: Determine the correct catch handler (if there exists one)
      for (exceptionType <- types) {
        findMatchingCatch(outerFuncName, exceptionType, catchStack) match {
          case Some(catchLabel) => {
            cases.addOne((exceptionType, gotoStm(catchLabel)))
          }
          case None => {
            // No handler can catch the exception
            if (outerFuncName == "main") {
              cases.addOne((exceptionType, abortStm))
            } else {
              cases.addOne((exceptionType, exceptionPropagationReturn(outerFuncName)))
            }
          }
        }
      }

      cases
    }

    private def switchForRethrow(
      outerFuncName: String,
      catchStack: Stack[ListBuffer[(Parameter_declaration, Int)]]
    ): Selection_stm = {
      // Use all possible exception types in switch statement
      val cases = switchExceptionCases(outerFuncName, catchStack, exceptionTypes)
      switchExceptionTypeCatch(cases)
    }

    private def exceptionPropagationReturn(funcName: String): Stm = {
      val retTypeListDeclSpec = funcReturnTypesMap.get(funcName) match {
        case Some(t) => t
        case None => throw new ExceptionTransformException("Missing return type for function " + funcName)
      }
      val typeSpecList = listDeclSpecToListOfTypeSpec(retTypeListDeclSpec)

      if (typeSpecList.size == 1) {
        typeSpecList(0) match {
          case t: Tvoid => {
            return emptyReturnStm
          }
          case _ => {}
        }
      }

      val listStm = new ListStm
      val listInitDecl = new ListInit_declarator
      val varName = "__ret_" + getId().toString()

      // Varible declaration and return statement
      listInitDecl.add(new OnlyDecl(new NoPointer(new Name(varName))))
      listStm.add(new DecS(new Declarators(retTypeListDeclSpec, listInitDecl, new ListExtra_specifier)))
      listStm.add(returnStm(new Evar(varName)))

      new CompS(new ScompTwo(listStm))
    }

    private def funcCallExceptionCheckIfStm(
      outerFuncName: String,
      entireStm: Stm,
      funcCallExp: Exp,
      catchStack: Stack[ListBuffer[(Parameter_declaration, Int)]],
    ): Stm = {
      val calledFuncName = funcCallExp.accept(getName, ())
      val funcExceptionTypes = funcExceptionTypeData.get(calledFuncName) match {
        case Some(v) => v
        case None => throw new ExceptionTransformException("Missing exceptiontype data for function")
      }

      if (funcExceptionTypes.isEmpty) {
        // No need to check exception if function cannot throw
        return new CompS(new ScompOne)
      }

      val cases = switchExceptionCases(outerFuncName, catchStack, funcExceptionTypes)
      val listStm = new ListStm
      listStm.add(new SelS(switchExceptionTypeCatch(cases)))
      new SelS(ifStm(new Evar(exceptionFlagVarName), new CompS(new ScompTwo(listStm)), None))
    }

    override def visit(
      expStm: ExprS,
      arg: (String, Stack[ListBuffer[(Parameter_declaration, Int)]], Option[Parameter_declaration])
    ): Stm = {
      val (funcName, catchStack, optCatchDecl) = arg

      val newStm = expStm.expression_stm_ match {
        case nonEmptyExpStm: SexprTwo => nonEmptyExpStm.exp_ match {
          case throwExp: EthrowOne => {
            val stmList = new ListStm
            val thrownType = typeOfThrownExp(throwExp.exp_)

            // Set global exception variables
            stmList.add(setExceptionFlag)
            stmList.add(setExceptionType(thrownType))
            stmList.add(setExceptionValue(thrownType, throwExp.exp_))

            findMatchingCatch(funcName, thrownType, catchStack) match {
              case Some(catchLabel) => {
                stmList.add(gotoStm(catchLabel))
              } case None => {
                  // No handler can catch the exception
                  if (funcName == "main") {
                    stmList.add(abortStm)
                  } else {
                    stmList.add(exceptionPropagationReturn(funcName))
                  }
              }
            }

            new CompS(new ScompTwo(stmList))
          }
          case emptyThrow: EthrowTwo => {
            val stmList = new ListStm
            stmList.add(setExceptionFlag)

            optCatchDecl match {
              case Some(catchDecl) => {
                catchDecl match {
                  case _: More => {
                    stmList.add(new SelS(switchForRethrow(funcName, catchStack)))
                  }
                  case _ => {
                    findMatchingCatch(funcName, paramDeclToTypeSpecList(catchDecl), catchStack) match {
                      case Some(catchLabel) => {
                        stmList.add(gotoStm(catchLabel))
                      } case None => {
                        // No handler can catch the exception
                        if (funcName == "main") {
                          stmList.add(abortStm)
                        } else {
                          stmList.add(exceptionPropagationReturn(funcName))
                        }
                      }
                    }
                  }
                }
              }
              case None => {
                // Empty throw statement not inside catch
                // no exception to rethrow
                stmList.add(abortStm)
              }
            }

            new CompS(new ScompTwo(stmList))
          }
          case eFunk @ (_: Efunk | _: Efunkpar) => {
            val stmList = new ListStm
            val calledFuncName = eFunk.accept(getName, ())

            if (funcExceptionTypeData.contains(calledFuncName)) {
              val exceptionCheckIfStm = funcCallExceptionCheckIfStm(funcName, expStm, eFunk, catchStack)
              stmList.add(expStm)
              stmList.add(exceptionCheckIfStm)
              new CompS(new ScompTwo(stmList))
            } else {
              expStm
            }
          }
          case eAssign: Eassign => eAssign.exp_2 match {
            case eFunk @ (_: Efunk | _: Efunkpar) => {
              val stmList = new ListStm
              val calledFuncName = eFunk.accept(getName, ())

              if (funcExceptionTypeData.contains(calledFuncName)) {
                val exceptionCheckIfStm = funcCallExceptionCheckIfStm(funcName, expStm, eFunk, catchStack)
                val lhs = eAssign.exp_1
                val assignOp = eAssign.assignment_op_

                val funcRetType = funcReturnTypesMap.get(calledFuncName) match {
                  case Some(v) => v
                  case None => throw new ExceptionTransformException("Missing return type information for function" + calledFuncName)
                }

                val retVarName = "__" + calledFuncName + "_ret_" + getId()
                stmList.add(declarationAssignmentStm(funcRetType, retVarName, eFunk))
                stmList.add(exceptionCheckIfStm)
                stmList.add(new ExprS(new SexprTwo(new Eassign(lhs, assignOp, new Evar(retVarName)))))
                new CompS(new ScompTwo(stmList))
              } else {
                expStm
              }
            }
            case _ => expStm
          }
          case _ => expStm
        }
        case _ => expStm
      }

      copyLocationInformation(expStm, newStm)
    }

    override def visit(
      tryCatchStm: TryCatchS,
      arg: (String, Stack[ListBuffer[(Parameter_declaration, Int)]], Option[Parameter_declaration])
    ): Stm = {
      val (funcName, catchStack, optCatchDecl) = arg
      val stmList = new ListStm
      val catchTypes = new ListBuffer[(Parameter_declaration, Int)]
      val (tryBlock, catchBlocks) = tryCatchStm.try_stm_ match {
        case tryStm: Stry => (tryStm.compound_stm_, tryStm.listcatch_stm_)
      }

      // Collect the types from catch handlers
      for ((catchBlock, i) <- catchBlocks.asScala.view.zipWithIndex) {
        catchBlock match {
          case catchStm: Scatch => {
            val paramDecl = catchStm.parameter_declaration_

            paramDecl match {
              case catchAll: More => {
                // Check if a catch-all handler is used at a wrong position
                if (i != catchBlocks.size - 1)
                  throw new ExceptionTransformException("Catch-all can only be the last handler")
              }
              case _ => {}
            }
            catchTypes.addOne((paramDecl, getId))
          }
        }
      }

      val catchStackCopy = catchStack.clone()
      val tryId = getId()
      catchStackCopy.push(catchTypes)

      // Transform try block
      val tryStmList = new ListStm
      tryBlock match {
        case empty: ScompOne => {}
        case sCompTwo: ScompTwo => {
          val newSComp = sCompTwo.accept(this, (funcName, catchStackCopy, optCatchDecl))
          newSComp match {
            case _: ScompOne => {}
            case newSCompTwo: ScompTwo => {
              for (stm <- newSCompTwo.liststm_.asScala) {
                tryStmList.add(stm)
              }
            }
          }
        }
      }

      tryStmList.add(gotoStm(afterCatchLabelName(funcName, tryId)))
      val newTryBlock = new ScompTwo(tryStmList)
      stmList.add(new CompS(newTryBlock))

      val iter = catchTypes.iterator

      // Transform catch handler
      for (catchBlock <- catchBlocks.asScala) {
        val catchStmList = new ListStm
        val (_, blockId) = iter.next
        catchBlock match {
          case catchStm: Scatch => {
            val paramDecl = catchStm.parameter_declaration_
            val compoundStm = catchStm.compound_stm_
            val blockName = catchBlockLabelName(funcName, paramDecl, blockId)

            compoundStm match {
              case empty: ScompOne => {}
              case sCompTwo: ScompTwo => {
                // Declaration for exception value
                paramDecl match {
                  case typeAndParam: TypeAndParam => {
                    val varName = paramDecl.accept(getName, ())
                    catchStmList.add(
                      declarationAssignmentStm(
                        typeAndParam.listdeclaration_specifier_,
                        varName,
                        new Eselect(
                          new Evar(
                            exceptionValueVarName
                          ),
                          createExceptionStructField(typeAndParam.listdeclaration_specifier_)
                        )
                      )
                    )
                  }
                  case _ => {}
                }

                // Reset exception flag
                catchStmList.add(unsetExceptionFlag)

                // Transform the block
                val newSComp = sCompTwo.accept(this, (funcName, catchStack, Some(paramDecl)))
                newSComp match {
                  case _: ScompOne => {}
                  case newSCompTwo: ScompTwo => {
                    for (stm <- newSCompTwo.liststm_.asScala) {
                      catchStmList.add(stm)
                    }
                  }
                }
              }
            }
            catchStmList.add(gotoStm(afterCatchLabelName(funcName, tryId)))
            val newCatchBlock = new LabelS(new SlabelOne(blockName, new CompS(new ScompTwo(catchStmList))))
            stmList.add(newCatchBlock)
          }
        }
      }

      // Add a label for after the handlers
      stmList.add(emptyLabelStm(afterCatchLabelName(funcName, tryId)))
      copyLocationInformation(tryCatchStm, new CompS(new ScompTwo(stmList)))
    }

    override def visit(
      compStm: ScompTwo,
      arg: (String, Stack[ListBuffer[(Parameter_declaration, Int)]], Option[Parameter_declaration])
    ): ScompTwo = {
      val stms = new ListStm

      for (stm <- compStm.liststm_.asScala) {
        stm match {
          case tryStm: TryCatchS => {
            val transformedTryStm = tryStm.accept(this, arg)

            transformedTryStm match {
              case compS: CompS => compS.compound_stm_ match {
                case sCompTwo: ScompTwo => {
                  for (s <- sCompTwo.liststm_.asScala) {
                    stms.add(s)
                  }
                } 
                case _ => {}
              }
              case _ => throw new ExceptionTransformException("Invalid stm for transformed try stm")
            }
          }
          case _ => {
            stms.add(stm.accept(this, arg))
          }
        }
      }

      copyLocationInformation(compStm, new ScompTwo(stms))
    }
  }
}
