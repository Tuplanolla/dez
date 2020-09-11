HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

THRIFT:=thrift
THRIFTFLAGS:=-r
CXX:=g++
CXXFLAGS:=-I gen-cpp -I ../fungus -O2 -g -std=c++11 -lthrift

IDLPATTERN:=\<\([^[:space:]]\+\)\.\(idl\)\>
CXXPATTERN:=\<\([^[:space:]]\+\)\.\(cpp\)\>

CXXFILES:=$(shell cat _CXXFiles 2> /dev/null)
HXXFILES:=$(shell cat _HXXFiles 2> /dev/null)

VPATH:=.:gen-cpp

all :: main
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN MAKE
	$(HIDE) $(RM) .Makefile.d _CXXFiles _HXXFiles
	$(SHOW) echo CLEAN CXX
	$(HIDE) $(RM) main
	$(HIDE) $(RM) -r gen-cpp
	$(HIDE) find . -type f '(' \
	-name '*.o' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

run :: main
	$(SHOW) echo RUN $<
	$(HIDE) ./$<
.PHONY : run

main :: $(CXXFILES:.cpp=.o)
	$(SHOW) echo CXX -o $@
	$(HIDE) { cat _CXXFiles ; \
	sed 's#$(CXXPATTERN)#../fungus/\1.cpp#g' ../fungus/_CXXFiles ; \
	} | LC_ALL=C sort -u | \
	sed 's#$(CXXPATTERN)#\1.o#g' | \
	xargs $(CXX) $(CXXFLAGS) -o $@

%.o :: %.cpp .Makefile.d
	$(SHOW) echo CXX $<
	$(HIDE) $(CXX) $(CXXFLAGS) -c -o $@ $<

Makefile :: .Makefile.d
	$(SHOW) echo MAKE $@

.Makefile.d :: _CXXFiles _HXXFiles
	$(SHOW) echo CXX -MF $@
	$(HIDE) cat $^ | xargs $(CXX) $(CXXFLAGS) -MM -MF $@

# We begrudgingly allow C++ header files to have the extension `.h`.
_CXXFiles _HXXFiles &:: ../flower/_IDLFiles
	$(SHOW) echo THRIFT $<
	$(HIDE) for x in $$(sed 's#$(IDLPATTERN)#../flower/\1.idl#g' $^) ; \
	do $(THRIFT) $(THRIFTFLAGS) --gen cpp $$x ; \
	done
	$(SHOW) echo MAKE _CXXFiles _HXXFiles
	$(HIDE) find . gen-cpp -maxdepth 1 -type f '(' \
	-name '*.cpp' -o \
	-false ')' > _CXXFiles
	$(HIDE) find . gen-cpp -maxdepth 1 -type f '(' \
	-name '*.h' -o -name '*.hpp' -o \
	-false ')' > _HXXFiles

-include .Makefile.d
