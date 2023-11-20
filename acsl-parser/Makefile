PARSER_BASEDIR=$(shell pwd)
PARSER_LIBDIR=$(PARSER_BASEDIR)/../cc-parser/lib
PARSER_BINDIR=$(PARSER_BASEDIR)/bin

CUP = java_cup.Main
CUPFLAGS = -expect 7 -locations
CUP_JAR = $(PARSER_LIBDIR)/java-cup-11b.jar

JFLEX = jflex.Main
JFLEX_PLUGIN_JAR = $(PARSER_LIBDIR)/jflex-1.9.1.jar

LATEX = latex
DVIPS = dvips
DVIPDF = dvipdfm

CLASSPATH:=$(CLASSPATH):$(CUP_JAR):$(JFLEX_PLUGIN_JAR)
export CLASSPATH

JAVAC:=javac
JAVAC_FLAGS:=-target 1.8 -source 1.8

JAVA:=java
JAVA_FLAGS:=

.PHONY: all
all: download-jars acsl-parser.jar tricera/acsl/Test.class

include $(PARSER_BASEDIR)/../cc-parser/download_jars.mk

acsl-parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/tricera/acsl/Absyn/acsl.class $(PARSER_BINDIR)/tricera/acsl/sym.class $(PARSER_BINDIR)/tricera/acsl/Yylex.class $(PARSER_BINDIR)/tricera/acsl/PrettyPrinterNonStatic.class $(PARSER_BINDIR)/tricera/acsl/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/acsl-parser.jar tricera

$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

.PHONY: clean
clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf tricera
	rm -rf acsl.tex acsl.dvi acsl.aux acsl.log acsl.ps


# just any of the files that is created by bnfc
acsl.tex: acsl.cf
	bnfc -p tricera --java --jflex -l acsl.cf

$(PARSER_BINDIR)/tricera/acsl/Absyn/acsl.java: acsl.cf
	bnfc -p tricera --java --jflex -l acsl.cf

$(PARSER_BINDIR)/tricera/acsl/Absyn/acsl.class: $(PARSER_BINDIR)/tricera/acsl/Absyn/acsl.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/acsl/Absyn/*.java

tricera/acsl/Yylex.java: tricera/acsl/Yylex
#       remove some quotes that JLex does not accept
#	sed 's/\\\^/\^/g' <tricera/acsl/Yylex >tricera/acsl/Yylex.temp
#	mv tricera/acsl/Yylex.temp smtlib/Yylex
#       quote dashes "-"
#	sed 's/\\\+-/\\+\\-/g' <tricera/acsl/Yylex >tricera/acsl/Yylex.temp
#	mv tricera/acsl/Yylex.temp tricera/acsl/Yylex
	${JAVA} ${JAVA_FLAGS} ${JFLEX} tricera/acsl/Yylex

tricera/acsl/sym.java tricera/acsl/parser.java: tricera/acsl/_cup.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} tricera/acsl/_cup.cup
	mv sym.java parser.java tricera/acsl

$(PARSER_BINDIR)/tricera/acsl/Yylex.class: tricera/acsl/Yylex.java tricera/acsl/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/acsl/Yylex.java

$(PARSER_BINDIR)/tricera/acsl/sym.class: tricera/acsl/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/acsl/sym.java

$(PARSER_BINDIR)/tricera/acsl/parser.class: tricera/acsl/parser.java tricera/acsl/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/acsl/parser.java

tricera/acsl/PrettyPrinterNonStatic.java: tricera/acsl/PrettyPrinter.java
	sed 's/PrettyPrinter/PrettyPrinterNonStatic/g' <tricera/acsl/PrettyPrinter.java | sed 's/static//g' >tricera/acsl/PrettyPrinterNonStatic.java

$(PARSER_BINDIR)/tricera/acsl/PrettyPrinter.class: tricera/acsl/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/acsl/PrettyPrinter.java

$(PARSER_BINDIR)/tricera/acsl/PrettyPrinterNonStatic.class: tricera/acsl/PrettyPrinterNonStatic.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/acsl/PrettyPrinterNonStatic.java

tricera/acsl/Test.class: tricera/acsl/Test.java $(PARSER_BINDIR)/tricera/acsl/PrettyPrinter.class $(PARSER_BINDIR)/tricera/acsl/Yylex.class $(PARSER_BINDIR)/tricera/acsl/parser.class $(PARSER_BINDIR)/tricera/acsl/sym.class
	${JAVAC} ${JAVAC_FLAGS} tricera/acsl/Test.java

acsl.dvi: acsl.tex
	${LATEX} acsl.tex

acsl.pdf: acsl.dvi
	${DVIPDF} acsl.dvi

acsl.ps: acsl.dvi
	${DVIPS} acsl.dvi -o acsl.ps
