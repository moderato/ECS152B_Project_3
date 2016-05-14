CC = g++
all:
	$(CC) p2pim.c EncryptionLibrary.cpp -o p2pim
clean: 
	rm -rf *o p2pim
