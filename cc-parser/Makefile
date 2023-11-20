PARSER_BASEDIR=$(shell pwd)
PARSER_LIBDIR=$(PARSER_BASEDIR)/lib
PARSER_BINDIR=$(PARSER_BASEDIR)/bin

CUP = java_cup.Main
CUPFLAGS = -expect 100 -locations
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
all: download-jars cc-parser.jar tricera/concurrency/concurrent_c/Test.class

include $(PARSER_BASEDIR)/download_jars.mk

cc-parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/tricera/concurrency/concurrent_c/Absyn/concurrent_c.class $(PARSER_BINDIR)/tricera/concurrency/concurrent_c/sym.class $(PARSER_BINDIR)/tricera/concurrency/concurrent_c/Yylex.class $(PARSER_BINDIR)/tricera/concurrency/concurrent_c/PrettyPrinterNonStatic.class $(PARSER_BINDIR)/tricera/concurrency/concurrent_c/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/cc-parser.jar tricera


$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

.PHONY: clean
clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf tricera
	rm -rf concurrent_c.tex concurrent_c.dvi concurrent_c.aux concurrent_c.log concurrent_c.ps


# just any of the files that is created by bnfc
concurrent_c.tex: concurrentC.cf
	bnfc -p tricera.concurrency --java --jflex -l concurrentC.cf

$(PARSER_BINDIR)/tricera/concurrency/concurrent_c/Absyn/concurrent_c.java: concurrentC.cf
	bnfc -p tricera.concurrency --java --jflex -l concurrentC.cf

$(PARSER_BINDIR)/tricera/concurrency/concurrent_c/Absyn/concurrent_c.class: $(PARSER_BINDIR)/tricera/concurrency/concurrent_c/Absyn/concurrent_c.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrent_c/Absyn/*.java

tricera/concurrency/concurrent_c/Yylex.java: tricera/concurrency/concurrent_c/Yylex
#       remove some quotes that JLex does not accept
#	sed 's/\\\^/\^/g' <tricera/concurrency/concurrent_c/Yylex >tricera/concurrency/concurrent_c/Yylex.temp
#	mv tricera/concurrency/concurrent_c/Yylex.temp smtlib/Yylex
#       quote dashes "-"
#	sed 's/\\\+-/\\+\\-/g' <tricera/concurrency/concurrent_c/Yylex >tricera/concurrency/concurrent_c/Yylex.temp
#	mv tricera/concurrency/concurrent_c/Yylex.temp tricera/concurrency/concurrent_c/Yylex
	${JAVA} ${JAVA_FLAGS} ${JFLEX} tricera/concurrency/concurrent_c/Yylex

tricera/concurrency/concurrent_c/sym.java tricera/concurrency/concurrent_c/parser.java: tricera/concurrency/concurrent_c/_cup.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} tricera/concurrency/concurrent_c/_cup.cup
	mv sym.java parser.java tricera/concurrency/concurrent_c/

$(PARSER_BINDIR)/tricera/concurrency/concurrent_c/Yylex.class: tricera/concurrency/concurrent_c/Yylex.java tricera/concurrency/concurrent_c/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrent_c/Yylex.java

$(PARSER_BINDIR)/tricera/concurrency/concurrent_c/sym.class: tricera/concurrency/concurrent_c/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrent_c/sym.java

$(PARSER_BINDIR)/tricera/concurrency/concurrent_c/parser.class: tricera/concurrency/concurrent_c/parser.java tricera/concurrency/concurrent_c/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrent_c/parser.java

tricera/concurrency/concurrent_c/PrettyPrinterNonStatic.java: tricera/concurrency/concurrent_c/PrettyPrinter.java
	sed 's/PrettyPrinter/PrettyPrinterNonStatic/g' <tricera/concurrency/concurrent_c/PrettyPrinter.java | sed 's/static//g' >tricera/concurrency/concurrent_c/PrettyPrinterNonStatic.java

$(PARSER_BINDIR)/tricera/concurrency/concurrent_c/PrettyPrinter.class: tricera/concurrency/concurrent_c/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrent_c/PrettyPrinter.java

$(PARSER_BINDIR)/tricera/concurrency/concurrent_c/PrettyPrinterNonStatic.class: tricera/concurrency/concurrent_c/PrettyPrinterNonStatic.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrent_c/PrettyPrinterNonStatic.java

tricera/concurrency/concurrent_c/Test.class: tricera/concurrency/concurrent_c/Test.java $(PARSER_BINDIR)/tricera/concurrency/concurrent_c/PrettyPrinter.class $(PARSER_BINDIR)/tricera/concurrency/concurrent_c/Yylex.class $(PARSER_BINDIR)/tricera/concurrency/concurrent_c/parser.class $(PARSER_BINDIR)/tricera/concurrency/concurrent_c/sym.class
	${JAVAC} ${JAVAC_FLAGS} tricera/concurrency/concurrent_c/Test.java

concurrent_c.dvi: concurrent_c.tex
	${LATEX} concurrent_c.tex

concurrent_c.pdf: concurrent_c.dvi
	${DVIPDF} concurrent_c.dvi

concurrent_c.ps: concurrent_c.dvi
	${DVIPS} concurrent_c.dvi -o concurrent_c.ps
