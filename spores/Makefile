HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

THRIFT:=thrift
CXX:=g++
CXXFLAGS:=-I gen-cpp -O2

all :: main gen-cpp
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN CXX
	$(HIDE) $(RM) main
	$(HIDE) find . -type f '(' \
	-name '*.o' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

run :: main
	$(SHOW) echo RUN $<
	$(HIDE) ./$<
.PHONY : run

main :: main.o
	$(CXX) $(CXXFLAGS) -o $@ $<

main.o :: main.cxx
	$(CXX) $(CXXFLAGS) -c -o $@ $<

gen-cpp :: ../flower/gen.idl
	$(SHOW) echo THRIFT $<
	$(HIDE) $(THRIFT) --gen cpp -r $<

# TODO Unify with `_MLFiles` convention.
