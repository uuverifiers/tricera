

CUP = java_cup.Main
CUPFLAGS = -nopositions -expect 100

JLEX = JLex.Main

LATEX = latex
DVIPS = dvips
DVIPDF = dvipdfm


PARSER_BASEDIR=$(shell pwd)
PARSER_BINDIR=$(PARSER_BASEDIR)/bin


JLEX_PATH:=/usr/share/java/JLex.jar
CLASSPATH:=$(CLASSPATH):$(PARSER_BASEDIR)/lib/java-cup-11a.jar:$(PARSER_BASEDIR):$(JLEX_PATH)

JAVAC:=javac
#JAVAC_FLAGS:=-target 1.5

JAVA:=java
JAVA_FLAGS:=


export CLASSPATH


all: cc-parser.jar tricera/concurrency/concurrentC/Test.class


cc-parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/tricera/concurrency/concurrentC/Absyn/concurrentC.class $(PARSER_BINDIR)/tricera/concurrency/concurrentC/sym.class $(PARSER_BINDIR)/tricera/concurrency/concurrentC/Yylex.class $(PARSER_BINDIR)/tricera/concurrency/concurrentC/PrettyPrinterNonStatic.class $(PARSER_BINDIR)/tricera/concurrency/concurrentC/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/cc-parser.jar tricera


$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf tricera
	rm -rf concurrentC.tex concurrentC.dvi concurrentC.aux concurrentC.log concurrentC.ps


# just any of the files that is created by bnfc
concurrentC.tex: concurrentC.cf
	bnfc -p tricera.concurrency -java1.5 concurrentC.cf

$(PARSER_BINDIR)/tricera/concurrency/concurrentC/Absyn/concurrentC.java: concurrentC.cf
	bnfc -p tricera.concurrency -java1.5 concurrentC.cf

$(PARSER_BINDIR)/tricera/concurrency/concurrentC/Absyn/concurrentC.class: $(PARSER_BINDIR)/tricera/concurrency/concurrentC/Absyn/concurrentC.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrentC/Absyn/*.java

tricera/concurrency/concurrentC/Yylex.java: tricera/concurrency/concurrentC/Yylex
#       remove some quotes that JLex does not accept
#	sed 's/\\\^/\^/g' <smtlib/Yylex >smtlib/Yylex.temp
#	mv smtlib/Yylex.temp smtlib/Yylex
#       quote dashes "-"
#	sed 's/\\\+-/\\+\\-/g' <smtlib/Yylex >smtlib/Yylex.temp
#	mv smtlib/Yylex.temp smtlib/Yylex
	${JAVA} ${JAVA_FLAGS} ${JLEX} tricera/concurrency/concurrentC/Yylex

tricera/concurrency/concurrentC/sym.java tricera/concurrency/concurrentC/parser.java: tricera/concurrency/concurrentC/concurrentC.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} tricera/concurrency/concurrentC/concurrentC.cup
	mv sym.java parser.java tricera/concurrency/concurrentC/

$(PARSER_BINDIR)/tricera/concurrency/concurrentC/Yylex.class: tricera/concurrency/concurrentC/Yylex.java tricera/concurrency/concurrentC/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrentC/Yylex.java

$(PARSER_BINDIR)/tricera/concurrency/concurrentC/sym.class: tricera/concurrency/concurrentC/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrentC/sym.java

$(PARSER_BINDIR)/tricera/concurrency/concurrentC/parser.class: tricera/concurrency/concurrentC/parser.java tricera/concurrency/concurrentC/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrentC/parser.java

tricera/concurrency/concurrentC/PrettyPrinterNonStatic.java: tricera/concurrency/concurrentC/PrettyPrinter.java
	sed 's/PrettyPrinter/PrettyPrinterNonStatic/g' <tricera/concurrency/concurrentC/PrettyPrinter.java | sed 's/static//g' >tricera/concurrency/concurrentC/PrettyPrinterNonStatic.java

$(PARSER_BINDIR)/tricera/concurrency/concurrentC/PrettyPrinter.class: tricera/concurrency/concurrentC/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrentC/PrettyPrinter.java

$(PARSER_BINDIR)/tricera/concurrency/concurrentC/PrettyPrinterNonStatic.class: tricera/concurrency/concurrentC/PrettyPrinterNonStatic.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) tricera/concurrency/concurrentC/PrettyPrinterNonStatic.java

tricera/concurrency/concurrentC/Test.class: tricera/concurrency/concurrentC/Test.java $(PARSER_BINDIR)/tricera/concurrency/concurrentC/PrettyPrinter.class $(PARSER_BINDIR)/tricera/concurrency/concurrentC/Yylex.class $(PARSER_BINDIR)/tricera/concurrency/concurrentC/parser.class $(PARSER_BINDIR)/tricera/concurrency/concurrentC/sym.class
	${JAVAC} ${JAVAC_FLAGS} tricera/concurrency/concurrentC/Test.java

concurrentC.dvi: concurrentC.tex
	${LATEX} concurrentC.tex

concurrentC.pdf: concurrentC.dvi
	${DVIPDF} concurrentC.dvi

concurrentC.ps: concurrentC.dvi
	${DVIPS} concurrentC.dvi -o concurrentC.ps
