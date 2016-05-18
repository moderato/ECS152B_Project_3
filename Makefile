CC = g++
all:
	$(CC) -std=c++11 p2pim.c EncryptionLibrary.cpp -o p2pim
clean: 
	rm -rf *o p2pim
