all: FOL/Test
	echo ""

FOL/Test.hs FOL/Lex.x FOL/Layout.hs FOL/Par.y : FOL.cf
	bnfc --haskell -d $<

FOL/Par.hs: FOL/Par.y
	happy -gcai $<
	

FOL/Lex.hs: FOL/Lex.x
	alex -g $<

FOL/Test: FOL/Test.hs FOL/Par.hs FOL/Lex.hs
	ghc --make $< -o $@

clean:
	-rm -f FOL/*.log FOL/*.aux FOL/*.hi FOL/*.o FOL/*.dvi
	-rm -f *.hi *.o gfg 

distclean: clean
	-rm -f FOL/*
	-rmdir -p FOL/

# EOF
