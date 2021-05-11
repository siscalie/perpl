all: compiler.exe

compiler.exe: *.hs
	ghc Main.hs --make -o compiler.exe

parse-test: compiler.exe
	./compiler.exe < example.ppl

clean:
	rm -f *.o *.hi *.exe
