#ifndef USERLIST_H
#define USERLIST_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define STRING_SIZE 256

struct User{
    int TCPfd;
    int UDPport;
    int TCPport;
    char Username[STRING_SIZE];
    char Hostname[STRING_SIZE];
    struct User* nextUser;
};

struct User *head = (struct User *) NULL;
struct User *end = (struct User *) NULL;

struct User* initUser(int UDPport, int TCPport, char* Hostname, char* Username){
    struct User *ptr;
    ptr = (struct User *) malloc(sizeof(struct User));
    if(ptr == NULL){
    	printf("Fail to allocate!\n");
        return (struct User *) NULL;
    }
    else{
    	ptr->TCPfd = -1;
    	ptr->UDPport = UDPport;
    	ptr->TCPport = TCPport;
        strcpy(ptr->Username, Username);
        strcpy(ptr->Hostname, Hostname);
        ptr->nextUser = NULL;
        return ptr;                         
    }
}

int getUserNum(){
    int num = 0;
    if(head == NULL)
        return num;
    struct User* ptr = head;
    while(ptr != NULL){
        ptr = ptr->nextUser;
        num++;
    }
    return num;
}

struct User* searchUser(char* Username){
	struct User* temp = head;
    while(temp != NULL && strcmp(Username, temp->Username)){
    	temp = temp->nextUser;
    }
    return temp;
}

struct User* searchUserByNum(int num){
    int i = 0;
    struct User* temp = head;
    while(temp != NULL && i != num){
        i++;
        temp = temp->nextUser;
    }
    return temp;
}

struct User* searchUserByTCP(int num){
    struct User* temp = head;
    while(temp != NULL && temp->TCPfd != num){
        temp = temp->nextUser;
    }
    return temp;
}

int inUserList(char* Username){
    if(searchUser(Username) != NULL){
        return 1;
    }
    return 0;
}

void printUser(char* Username)
{
    struct User* temp = NULL;
    temp = searchUser(Username);

    if(temp == NULL){
    	printf("No such user!\n");
    	return;
    }
    printf("TCP fd: %d, ", temp->TCPfd);
    printf("Host name: %s, ", temp->Hostname);
    printf("User name: %s, ", temp->Username);
    printf("UDP port: %d, ", temp->UDPport);
    printf("TCP port: %d\n", temp->TCPport);
}

void printList()
{
	struct User* ptr = head;
    int i = 0;
    if(ptr == NULL){
        printf("0 user in list.\n");
        return;
    }
    printf("%d user in list.\n", getUserNum());
    while(ptr != NULL){
        printf("%d. ", i++);
        printUser(ptr->Username);           
        ptr = ptr->nextUser;
    }
}

void addUser(struct User* ptr)
{
   	if(head == NULL){
   		head = ptr;
   	}
   	else{
		end->nextUser = ptr;
   	} 	
   	end = ptr;
}


void deleteUser(char* Username)
{
    struct User *temp, *prev;
    prev = head;
    temp = searchUser(Username);

    if(temp == NULL){
    	// printf("No such user!\n");
    	return;
    }
    
    if(temp == prev){
        head = head->nextUser;
        if(end == temp) 
           end = end->nextUser;
        free(temp);
    }
    else{
        while(prev->nextUser != temp){
            prev = prev->nextUser; 
        }
        prev->nextUser = temp->nextUser;
        if(end == temp)
            end = prev;
        free(temp);
    }
}


void deleteList(struct User *ptr)
{
    struct User *temp;

    if(head == NULL) return; 

    if(ptr == head){
        head = NULL;
        end = NULL;
    }
    else{
        temp = head;
        while(temp->nextUser != ptr)
            temp = temp->nextUser;
        end = temp;
    }

    while(ptr != NULL){
       temp = ptr->nextUser;
       free(ptr);
       ptr = temp;
    }
}

#endif