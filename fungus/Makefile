HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

CXX:=g++
CXXFLAGS:=-I gen-cpp -O2 -g -std=c++11

CXXFILES:=$(shell cat _CXXFiles 2> /dev/null)
HXXFILES:=$(shell cat _HXXFiles 2> /dev/null)

all :: $(CXXFILES:.cpp=.o)
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN MAKE
	$(HIDE) $(RM) .Makefile.d _CXXFiles _HXXFiles
	$(SHOW) echo CLEAN CXX
	$(HIDE) find . -type f '(' \
	-name '*.o' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

%.o :: %.cpp .Makefile.d
	$(SHOW) echo CXX $<
	$(HIDE) $(CXX) $(CXXFLAGS) -c -o $@ $<

Makefile :: .Makefile.d
	$(SHOW) echo MAKE $@

.Makefile.d :: _CXXFiles _HXXFiles
	$(SHOW) echo CXX -MF $@
	$(HIDE) cat $^ | xargs $(CXX) $(CXXFLAGS) -MM -MF $@

_CXXFiles :: $(CXXFILES)
	$(SHOW) echo MAKE $@
	$(HIDE) find . -maxdepth 1 -type f '(' \
	-name '*.cpp' -o \
	-false ')' > $@

_HXXFiles :: $(HXXFILES)
	$(SHOW) echo MAKE $@
	$(HIDE) find . -maxdepth 1 -type f '(' \
	-name '*.h' -o -name '*.hpp' -o \
	-false ')' > $@

-include .Makefile.d
