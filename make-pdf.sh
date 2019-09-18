lhs2TeX --poly arithmetic-code.lhs > arithmetic-code.tex 
rubber --pdf arithmetic-code 
(cd ~/work/arithmetic ;	make)   # lhs2Tex --math arithmetic.lhs > arithmetic.tex ; rubber --pdf arithmetic) 
(cd ~/work/arithmetic/ ; make publish)  #arithmetic.pdf ~/src/amen-calculator/ 
(cd ~/work/www ; make)


