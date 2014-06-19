OPT= -O2 -m32 -g

all: main32 main16 main4

main32: main32.o scaffold32.o myutil.o
	gcc $(OPT) -o main32 main32.o scaffold32.o myutil.o -lgmp -lrt

main32.o: main32.c scaffold32.h
	gcc $(OPT) -c main32.c

scaffold32.o: scaffold32.c scaffold32.h
	gcc $(OPT) -c scaffold32.c

main16: main16.o scaffold16.o myutil.o
	gcc $(OPT) -o main16 main16.o scaffold16.o myutil.o -lgmp -lrt

main16.o: main16.c scaffold16.h
	gcc $(OPT) -c main16.c

scaffold16.o: scaffold16.c scaffold16.h
	gcc $(OPT) -c scaffold16.c

main4: main4.o scaffold4.o myutil.o
	gcc $(OPT) -o main4 main4.o scaffold4.o myutil.o -lgmp -lrt

main4.o: main4.c scaffold4.h
	gcc $(OPT) -c main4.c

scaffold4.o: scaffold4.c scaffold4.h
	gcc $(OPT) -c scaffold4.c

myutil.o: myutil.c
	gcc $(OPT) -c myutil.c

clean: 
	rm *.o main4 main16 main32

# note! doesn't include your report file, if any
turnin: 
	echo Making `whoami`_`date '+%y-%m-%d'`.tar.gz 
	tar czvf `whoami`_`date '+%Y-%m-%d'`.tar.gz *.c *.h Makefile 
	
tar.gz: 
	tar czvf project_scaffold.tar.gz *.c *.h Makefile Readme
#	tar czvf project_scaffold_`date '+%Y-%m-%d'`.tar.gz *.c *.h Makefile Readme
	chmod 644 project_scaffold.tar.gz
	
