all:
	ghc --make ./InterpreterMain.hs -o interpreter
clean:
	rm -f interpreter
	rm -f *.o
	rm -f *.hi

