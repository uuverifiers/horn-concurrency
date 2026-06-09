1: run bnfc
2: add to makefile:
## MANUAL FIXES ## (dont overwrite)
PARSER_BASEDIR=$(shell pwd)
PARSER_LIBDIR=$(PARSER_BASEDIR)/lib
CUP = java_cup.Main
CUP_JAR = $(PARSER_LIBDIR)/java-cup-11b.jar

JFLEX = jflex.Main
JFLEX_PLUGIN_JAR = $(PARSER_LIBDIR)/jflex-1.9.1.jar

CLASSPATH:=$(CLASSPATH):$(CUP_JAR):$(JFLEX_PLUGIN_JAR)
export CLASSPATH

## /End manual fixes ##
3: run make