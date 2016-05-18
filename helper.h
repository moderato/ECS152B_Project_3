#ifndef HELPER_H
#define HELPER_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <dirent.h>
#include <signal.h>
#include <errno.h>
#include <termios.h>
#include <ctype.h>

#define BUFFER_SIZE 512
#define MAX_FD      50
#define _64CHAR     0
#define _CHAR64     1
#define SPECSOCKNUM 3

#define DUMMY       0x0000
#define DISCOVERY   0x0001
#define REPLY       0x0002
#define CLOSING     0x0003
#define ESTABLISH   0x0004
#define ACCEPT      0x0005
#define UNAVAILABLE 0x0006
#define USERLIST    0x0007
#define LISTREPLY   0x0008
#define DATA        0x0009
#define DISCONTINUE 0x000A
#define ESTABCRYPT  0x000B
#define ACCPTCRYPT  0x000C
#define DATACRYPT   0x000D  
#define REQAUTH     0x0010
#define AUTHREPLY   0x0011

constexpr uint16_t EncrTypes[11] = {0x0F0F, 0,      0,      0, 
				    0x5555, 0xAAAA, 0xFF00, 0x00FF,
				    0x5A5A, 0xA5A5, 0xF0F0};

extern char hostname[256];

// Print error
void error(const char *message){
    perror(message);
    exit(1);
}

// Return the first available fd in the polling array
int firstAvailableFD(struct pollfd* FDS){
    int i = 0;
    while(i == 2 || FDS[i].fd > 0){
        i++;
        if(i >= MAX_FD){
            printf("No available fd\n");
            return -1;
        }
    }
    return i;
}

// Search for a specific file descriptor
int searchFD(int fd, struct pollfd* FDS){
	int i = 3;
	while(FDS[i].fd != fd){
		i++;
		if(i >= MAX_FD)
			return -1;
	}
	return i;
}

// Display message
void DisplayMessage(char *data, int length){
    int Offset = 0;
    int Index;
    
    while(Offset < length){
        printf("%04X ", Offset);
        for(Index = 0; Index < 16; Index++){
            if((Offset + Index) < length){
                printf("%02X ",data[Offset + Index]);
            }
            else{
                printf("   ");
            }
        }
        for(Index = 0; Index < 16; Index++){
            if((Offset + Index) < length){
                if((' ' <= data[Offset + Index])&&(data[Offset + Index] <= '~')){
                    printf("%c",data[Offset + Index]);
                }
                else{
                    printf(".");
                }
            }
            else{
                printf(" ");
            }
        }
        printf("\n");
        Offset += 16;
    }
    printf("\n");
}

// Convert a char array to a uint64_t
void Char64_64Char(char* buf, uint64_t& num, int i){
    if(i == _CHAR64){
	uint64_t tmp = *(uint64_t *)buf;
	num = ntohl(tmp);
	num = num << 32;
	num += ntohl(tmp >> 32);
        return;
    }
    if(i == _64CHAR){
	for(int c = 0; c < 8; c++){
	    buf[7-c] = num >> (8 * c);
	}
        return;
    }
}

// Prepare header
int header(char* message, uint16_t type, int UDPport, int TCPport, char* Username){
    int length = 0;
    uint16_t conversion = 0;
    uint32_t conversionL = 0;
    char* temp = message;
    conversion = htons(type);
    message[0] = 'P';
    message[1] = '2';
    message[2] = 'P';
    message[3] = 'I';                      
    temp += 4;
    memcpy(temp, &conversion, 2);                
    temp += 2;
    length = temp - message;
    switch(type){
        case DISCOVERY:
        case REPLY:
        case CLOSING:
            conversion = htons(UDPport);
            memcpy(temp, &conversion, 2); 
            temp += 2;
            conversion = htons(TCPport);
            memcpy(temp, &conversion, 2); 
            temp += 2;
            memcpy(temp, hostname, strlen(hostname));
            temp += strlen(hostname);
            *temp = 0;
            temp += 1;
            memcpy(temp, Username, strlen(Username));
            temp += strlen(Username);
            *temp = 0;
            temp += 1;
            length = temp - message;
            break;
        case ESTABLISH:
        case EncrTypes[ESTABLISH]:
        case ESTABCRYPT:
            memcpy(temp, Username, strlen(Username));
            temp += strlen(Username);
            *temp = 0;
            temp += 1;
            length = temp - message;
            break;
        case ACCEPT:
        case UNAVAILABLE:
        case USERLIST:
        case DATA:
        case DISCONTINUE:
        case EncrTypes[ACCEPT]:
        case EncrTypes[UNAVAILABLE]:
        case EncrTypes[USERLIST]:
        case EncrTypes[DATA]:
        case EncrTypes[DISCONTINUE]:
        case REQAUTH:
        case ACCPTCRYPT:
        case DATACRYPT:
            break;
        case LISTREPLY:{    
            conversionL = htonl(getUserNum());
            memcpy(temp, &conversionL, 4);
            temp += 4;
            struct User* ptr = head;
            if(ptr == NULL){
                printf("No users!\n");
                length = -1;
                break;
            }
            int count = -1;
            while(ptr != NULL){
                count++;
                conversionL = htonl(count);
                memcpy(temp, &conversionL, 4);
                temp += 4;
                conversion = htons(ptr->UDPport);
                memcpy(temp, &conversion, 2);
                temp += 2;
                memcpy(temp, ptr->Hostname, strlen(ptr->Hostname));
                temp += strlen(ptr->Hostname);
                *temp = 0;
                temp += 1;
                conversion = htons(ptr->TCPport);
                memcpy(temp, &conversion, 2);
                temp += 2;
                memcpy(temp, ptr->Username, strlen(ptr->Username));
                temp += strlen(ptr->Username);
                *temp = 0;
                temp += 1;
                ptr = ptr->nextUser;
            }
            length = temp - message;
            break;
        }
        default:
            length = -1;
            break;
    }
    return length;
}


#endif