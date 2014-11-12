SRC = matmul.c
OBJ = $(SRC:.c=.obj)

PLUGIN=EspFe

all: $(OBJ)

.c.obj: 
	cl /analyze:plugin  $(HAVOC_DLL_DIR)\$(PLUGIN).dll /analyze:log d.xml  -c -nologo $<
clean:
	del *.obj *.xml