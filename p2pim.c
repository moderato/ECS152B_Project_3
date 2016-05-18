#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <dirent.h>
#include <signal.h>
#include <sys/types.h> 
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <netinet/in.h>
#include <sys/poll.h>
#include <time.h>
#include <netdb.h>
#include <errno.h>
#include <termios.h>
#include <ctype.h>
#include "userlist.h"
#include "EncryptionLibrary.h"

#define BUFFER_SIZE 512
#define MAX_FD      50
#define _64CHAR     0
#define _CHAR64     1

// Packet type
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

// State of non-canonical mode
#define NORMAL      0x0000
#define TOCONNECT   0x0001
#define TOSPEAK     0x0002
#define INPUTMSG    0x0004
#define TODELETE    0x0008
#define TOCLOSE     0x0010
#define TOREQUEST   0x0020

// List reply subtype
#define ENTRY       0x0001
#define UDPPORT     0x0002
#define HOSTNAME    0x0003
#define TCPPORT     0x0004
#define USERNAME    0x0005

constexpr uint16_t EncrTypes[11] = {0x0F0F, 0,      0,      0, 
				    0x5555, 0xAAAA, 0xFF00, 0x00FF,
				    0x5A5A, 0xA5A5, 0xF0F0};

union u{
  uint64_t ui;
  unsigned char c[8];
};

const char* short_options = "p:h:";  
int UDPfd, TCPfd; // UDP and TCP server sockets
int TCPs[MAX_FD-3], msgLen[MAX_FD-3], zeroCount[MAX_FD-3]; // For each user
char hostname[256], *username; // Hostname and 
char messages[MAX_FD-3][BUFFER_SIZE]; // For each user
int uport = 50550, tport = 50551, authport = 50552, uitimeout = 5, umtimeout = 60; // For this machine
int nonCanState = NORMAL; // Non-canonical mode state
struct sockaddr_in BroadcastAddress, UserAddress; // For broadcasting and sending tcp
struct termios SavedTermAttributes; // For non canonical mode
struct pollfd fds[MAX_FD]; // Polling structures
struct User* activeUser = NULL; // Who are we talking to
char nonCanBuffer[BUFFER_SIZE]; // Buffer non-canonical mode input
int nonCanLength = 0; // Length of the buffered message
int listReplyCount;
int listReplySubtype;
uint64_t SecretNum, PublicKey, Modulus;
// All local buffers in functions are called buf

// Print error
void error(const char *message){
    perror(message);
    exit(1);
}

// Return the first available fd in the polling array
int firstAvailableFD(){
    int i = 0;
    while(i == 2 || fds[i].fd > 0){
        i++;
        if(i >= MAX_FD){
            printf("No available fd\n");
            return -1;
        }
    }
    return i;
}

// Search for a specific file descriptor
int searchFD(int fd){
	int i = 3;
	while(fds[i].fd != fd){
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

struct option long_options[] = {
    { "ap",           1,   NULL,    'p'     },
    { "ah",           1,   NULL,    'h'     },
    {    0,           0,      0,     0      },  
};

static void usage(void){
    printf(
        "Usage: p2pim [options]\n"
        "  -p,   --ap     Specify UDP port for trust anchor\n"
        "  -h,   --ah     Specify host (and port) for unicast\n"
    );
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

void ResetCanonicalMode(int fd, struct termios *savedattributes){
    tcsetattr(fd, TCSANOW, savedattributes);
}

void SetNonCanonicalMode(int fd, struct termios *savedattributes){
    struct termios TermAttributes;
    
    // Make sure stdin is a terminal. 
    if(!isatty(fd)){
        fprintf (stderr, "Not a terminal.\n");
        exit(0);
    }
    
    // Save the terminal attributes so we can restore them later. 
    tcgetattr(fd, savedattributes);
    
    // Set the funny terminal modes. 
    tcgetattr (fd, &TermAttributes);
    TermAttributes.c_lflag &= ~(ICANON | ECHO); // Clear ICANON and ECHO. 
    TermAttributes.c_cc[VMIN] = 1;
    TermAttributes.c_cc[VTIME] = 0;
    tcsetattr(fd, TCSAFLUSH, &TermAttributes);
}

// Need to be modified
void SignalHandler(int param){
    char buf[BUFFER_SIZE];
    int length = header(buf, CLOSING, uport, tport, username);
    int Result = sendto(UDPfd, buf, length, 0, (struct sockaddr *)&BroadcastAddress, sizeof(BroadcastAddress));
    if(0 > Result){
        error("ERROR send to client");
    }
    ResetCanonicalMode(STDIN_FILENO, &SavedTermAttributes);
    close(TCPfd);
    close(UDPfd);
    close(STDIN_FILENO); // Close up 3 most important socket.
    struct User* temp = head;
    while(temp != NULL){
        close(temp->TCPfd);
        temp = temp->nextUser;
    }
    if(head != NULL)
        deleteList(head);
    printf("Close up finished!\n");
    exit(0);
}

// Reset TCP buffers
void resetTCPbuf(int j){
    bzero(messages[j], BUFFER_SIZE);
    zeroCount[j] = 0;
    msgLen[j] = 0;
}

void TCPmsgProcess(int j, int *fd){
    int type, length, Result;
    char buf[BUFFER_SIZE];
    type = ntohs(*(uint16_t *)(messages[j]+4));
    switch(type){
        case ESTABLISH:
        case DATA:
            zeroCount[j] = 1;
            break;
        case ACCEPT:
            printf("Connection accepted!\n");
            resetTCPbuf(j);
        	break;
        case UNAVAILABLE:
            *fd = -1;
            printf("Connection unavailable\n");
            resetTCPbuf(j);
            break;
        case USERLIST:
            length = header(buf, LISTREPLY, uport, tport, username);
            DisplayMessage(buf, length);
            Result = write(*fd, buf, length);
            if(0 > Result){
	        	error("ERROR writing to socket");
            }
            bzero(messages[j], BUFFER_SIZE);
            zeroCount[j] = 0;
            msgLen[j] = 0;
            break;
        case DISCONTINUE:
            *fd = -1;
            resetTCPbuf(j);
            break;
        default:
            break;
    }
}

// Print information
void printInfo(){
	printf("Hostname is %s.\n", hostname);
	printf("Username is %s.\n", username);
	printf("UDP port is %d.\n", uport);
	printf("TCP port is %d.\n", tport);
        printf("UDP port for authentication is %d.\n", authport);
	printf("UDP initial timeout %d.\n", uitimeout);
	printf("UDP maximum timeout %d.\n", umtimeout);
}

void processCommand(char c){
    if(nonCanState == NORMAL){
    	switch(c){
	        case 'H': case 'h':
	            printf("Help:\n");
	            printf("C/c: Connect to a user in list\n");
	            printf("D/d: Delete a user in list\n");
	            printf("S/s: Speak to a user in list\n");
	            printf("N/n: Close a user in list\n");
	            printf("L/l: List users\n");
	            printf("R/r: Request User List\n");
	            printf("I/i: See info for this machine\n");
	            break;
	        case 'C': case 'c': // Connect to a user
	            if(getUserNum() != 0){
	                printf("Which one to connect? Input a number:\n");
	                nonCanState = TOCONNECT;
	            }
	            else{
	            	printf("No user to connect\n");
	            }
	            break;
	        case 'D': case 'd': // Delete a user
	            if(getUserNum() != 0){
	                printf("Which one to delete? Input a number:\n");
	                nonCanState = TODELETE;
	            }
	            else{
	            	printf("No user to delete\n");
	            }
	            break;
	        case 'S': case 's': // Speak to a user
	            if(getUserNum() != 0){
	                printf("Which one to speak? Input a number:\n");
	                nonCanState = TOSPEAK;
	            }
	            else{
	            	printf("No user to speak to\n");
	            }
	            break;
	        case 'L': case 'l': // List all the users
	        	printList();
	        	break;
	        case 'N': case 'n': // Close a user
	        	if(getUserNum() != 0){
	                printf("Which one to close? Input a number:\n");
	                nonCanState = TOCLOSE;
	            }
	            else{
	            	printf("No user to close\n");
	            }
	        	break;
	        case 'R': case 'r': // Request user list
	        	if(getUserNum() != 0){
	                printf("Which one to request user list? Input a number:\n");
	                nonCanState = TOREQUEST;
	            }
	            else{
	            	printf("No user to request\n");
	            }
	        	break;
	        case 'I': case 'i': // List all the users
	        	printInfo();
	        	break;
	        default:
	        	printf("Unknown command! Press 'h' to see help\n");
	        	nonCanState = NORMAL;
	            break;
	    }
    }
    else{
	    if(isprint(c)){
	        printf("RX: '%c' 0x%02X\n", c, c);
	    }
	    else{
	        printf("RX: ' ' 0x%02X\n", c);
	    }
    	switch(nonCanState){
    		case TOCONNECT:
    			if(c != '\n'){
    				nonCanBuffer[nonCanLength] = c;
    				nonCanLength++;
    			}
    			else{
    				int num;
    				if(nonCanLength == 1 && nonCanBuffer[0] == '0')
    					num = 0;
    				else{
    					num = atoi(nonCanBuffer);
    					if(num == 0 || num >= getUserNum()){
    						printf("Not a valid number\n");
    						bzero(nonCanBuffer, BUFFER_SIZE);
    						nonCanLength = 0;
    						nonCanState = NORMAL;
    						break;
    					}
    				}
					struct User* temp = searchUserByNum(num);
	                if(temp->TCPfd > 0){
	                    printf("Already connected! Press 's' to speak\n");
	                }
	                else{
		                temp->TCPfd = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
		                struct hostent* Client = gethostbyname(temp->Hostname);
		                if(NULL == Client){
		                    fprintf(stderr,"ERROR, no such host\n");
		                    exit(0);
		                }
		                bzero((char *) &UserAddress, sizeof(UserAddress));
		                UserAddress.sin_family = AF_INET;
		                bcopy((char *)Client->h_addr, (char *)&UserAddress.sin_addr.s_addr, Client->h_length);
		                UserAddress.sin_port = htons(temp->TCPport);
		                if(0 > connect(temp->TCPfd, (struct sockaddr *)&UserAddress, sizeof(UserAddress))){
		                    error("ERROR connecting");
		                }
		                
		                int first = firstAvailableFD();
		                fds[first].fd = temp->TCPfd;
		                fds[first].events = POLLIN | POLLPRI;
		                char buf[BUFFER_SIZE];
		                int length = header(buf, ESTABLISH, 0, 0, temp->Username);
		                // DisplayMessage(buf, length);
		                int Result = write(temp->TCPfd, buf, length);
		                if(0 > Result){
		                    error("ERROR writing to socket");
		                }
		            }
	                bzero(nonCanBuffer, BUFFER_SIZE);
    				nonCanLength = 0;
    				nonCanState = NORMAL;
    			}
    			break;
    		case TOSPEAK:
    			if(c != '\n'){
    				nonCanBuffer[nonCanLength] = c;
    				nonCanLength++;
    			}
    			else{
    				int num;
    				if(nonCanLength == 1 && nonCanBuffer[0] == '0')
    					num = 0;
    				else{
    					num = atoi(nonCanBuffer);
    					if(num == 0 || num >= getUserNum()){
    						printf("Not a valid number\n");
    						nonCanState = NORMAL;
    						bzero(nonCanBuffer, BUFFER_SIZE);
    						nonCanLength = 0;
    						break;
    					}
    				}
					struct User* temp = searchUserByNum(num);
	                if(temp->TCPfd <= 0){
	                    printf("Connection not established! Press 'c' to connect\n");
	                    nonCanState = NORMAL;
	                }
	                else{
	                	printf("Input the message:\n");
	                	activeUser = temp;
	                	nonCanState = INPUTMSG;
	                }
	                bzero(nonCanBuffer, BUFFER_SIZE);
    				nonCanLength = 0;
    			}
    			break;
    		case INPUTMSG:
    			if(c != '\n'){
    				nonCanBuffer[nonCanLength] = c;
    				nonCanLength++;
    			}
    			else{
    				char buf[BUFFER_SIZE];
	                int length = header(buf, DATA, 0, 0, NULL);
	                memcpy(buf+length, nonCanBuffer, strlen(nonCanBuffer));
	                length += strlen(nonCanBuffer);
	                buf[length++] = 0;
	                int Result = write(activeUser->TCPfd, buf, length);
	                if(0 > Result){
	                    error("ERROR writing to socket");
	                }
	                printf("Message sent: %s\n", buf+6);
	                bzero(nonCanBuffer, BUFFER_SIZE);
    				nonCanLength = 0;
    				nonCanState = NORMAL;
    				activeUser = NULL;
    			}
    			break;
    		case TODELETE:
    			if(c != '\n'){
    				nonCanBuffer[nonCanLength++] = c;
    			}
    			else{
    				int num;
    				if(nonCanLength == 1 && nonCanBuffer[0] == '0')
    					num = 0;
    				else{
    					num = atoi(nonCanBuffer);
    					if(num == 0 || num >= getUserNum()){
    						printf("Not a valid number\n");
    						bzero(nonCanBuffer, BUFFER_SIZE);
    						nonCanLength = 0;
    						nonCanState = NORMAL;
    						break;
    					}
    				}
    				struct User* temp = searchUserByNum(num);
    				close(temp->TCPfd);
    				printf("The following user is deleted!\n");
    				printUser(temp->Username);
    				deleteUser(temp->Username);
	                bzero(nonCanBuffer, BUFFER_SIZE);
    				nonCanLength = 0;
    				nonCanState = NORMAL;
    			}
    			break;
    		case TOCLOSE:
    			if(c != '\n'){
    				nonCanBuffer[nonCanLength] = c;
    				nonCanLength++;
    			}
    			else{
    				int num;
    				if(nonCanLength == 1 && nonCanBuffer[0] == '0')
    					num = 0;
    				else{
    					num = atoi(nonCanBuffer);
    					if(num == 0 || num >= getUserNum()){
    						printf("Not a valid number\n");
    						bzero(nonCanBuffer, BUFFER_SIZE);
    						nonCanLength = 0;
    						nonCanState = NORMAL;
    						break;
    					}
    				}
					struct User* temp = searchUserByNum(num);
	                if(temp->TCPfd <= 0){
	                    printf("Already closed\n");
	                }
	                else{
		                char buf[BUFFER_SIZE];
		                int length = header(buf, DISCONTINUE, 0, 0, NULL);
		                // DisplayMessage(buf, length);
		                int Result = write(temp->TCPfd, buf, length);
		                if(0 > Result){
		                    error("ERROR writing to socket");
		                }
		                int i = searchFD(temp->TCPfd);
		                temp->TCPfd = -1;
		                fds[i].fd = -1;
		            }
	                bzero(nonCanBuffer, BUFFER_SIZE);
    				nonCanLength = 0;
    				nonCanState = NORMAL;
    			}
    			break;
    		case TOREQUEST:
    			if(c != '\n'){
    				nonCanBuffer[nonCanLength] = c;
    				nonCanLength++;
    			}
    			else{
    				int num;
    				if(nonCanLength == 1 && nonCanBuffer[0] == '0')
    					num = 0;
    				else{
    					num = atoi(nonCanBuffer);
    					if(num == 0 || num >= getUserNum()){
    						printf("Not a valid number\n");
    						bzero(nonCanBuffer, BUFFER_SIZE);
    						nonCanLength = 0;
    						nonCanState = NORMAL;
    						break;
    					}
    				}
					struct User* temp = searchUserByNum(num);
	                if(temp->TCPfd <= 0){
	                    printf("Connection closed, press 'c' to connect\n");
	                }
	                else{
		                char buf[BUFFER_SIZE];
		                int length = header(buf, USERLIST, 0, 0, NULL);
		                // DisplayMessage(buf, length);
		                int Result = write(temp->TCPfd, buf, length);
		                if(0 > Result){
		                    error("ERROR writing to socket");
		                }
		                printf("User list request sent to '%s'\n", temp->Username);
		            }
	                bzero(nonCanBuffer, BUFFER_SIZE);
    				nonCanLength = 0;
    				nonCanState = NORMAL;
    			}
    			break;
    		default:
    			break;
    	}
    }
};

int main(int argc, char *argv[])
{
    int Result, rv, c, length;
    char recvBuffer[BUFFER_SIZE], sendBuffer[BUFFER_SIZE], password[BUFFER_SIZE];
    struct sockaddr_in ServerAddress, ClientAddress, AuthAddress;
    socklen_t ClientLength = sizeof(ClientAddress);
    int broadcast = 1, on = 1;
    int timeout = 0, restartDiscover = 1, anchorFound = 0;
    time_t start = time(NULL), diff;

    if(-1 == gethostname(hostname, 255)){
        error("No host name.\n");
        exit(1);
    }
    username = getenv("USER");
    memset(msgLen, 0, MAX_FD-3);
    memset(zeroCount, 0, MAX_FD-3);
    SecretNum = GenerateRandomValue();
    printf("%016X\n", SecretNum);
    printf("Enter password for %s> ", username);
    fgets(password, sizeof(password), stdin);

    while((c = getopt_long(argc, argv, short_options, long_options, NULL)) != -1){  
        switch (c)  
        {  
            case 'p':
                authport = atoi(optarg);
                break;
            case 'h':
                printf("%s\n", optarg);
                break;
            default:
                usage();
                exit(0);
        }  
    }
    printInfo();

    if(-1 == gethostname(hostname, 255)){
        error("No host name");
        exit(1);
    }

    signal(SIGTERM, SignalHandler);
    signal(SIGINT, SignalHandler);

    UDPfd = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
    if(0 > UDPfd){
        error("ERROR opening UDP socket");
    }
    if((setsockopt(UDPfd, SOL_SOCKET, SO_BROADCAST, &broadcast, sizeof(broadcast))) == -1){
        perror("setsockopt - SOL_SOCKET ");
        exit(1);
    }

    bzero((char *) &ServerAddress, sizeof(ServerAddress));
    ServerAddress.sin_family = AF_INET;
    ServerAddress.sin_addr.s_addr = INADDR_ANY;
    ServerAddress.sin_port = htons(uport);

    bzero((char *) &BroadcastAddress, sizeof(BroadcastAddress));
    BroadcastAddress.sin_family = AF_INET;
    BroadcastAddress.sin_addr.s_addr = INADDR_BROADCAST;
    BroadcastAddress.sin_port = htons(uport);

    if(0 > bind(UDPfd, (struct sockaddr *)&ServerAddress, sizeof(ServerAddress))){
        error("ERROR on binding");
    }

    TCPfd = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
    if(0 > TCPfd){
        error("ERROR opening TCP socket");
        exit(1);
    }

    Result = setsockopt(TCPfd, SOL_SOCKET,  SO_REUSEADDR, (char *)&on, sizeof(on));
    if(0 > Result){
        error("Error setting socket reusable");
        exit(1);
    }

    Result = ioctl(TCPfd, FIONBIO, (char *)&on);
    if(0 > Result){
        error("ioctl failed");
        exit(1);
    }

    bzero((char *) &ServerAddress, sizeof(ServerAddress));
    ServerAddress.sin_family = AF_INET;
    ServerAddress.sin_addr.s_addr = INADDR_ANY;
    ServerAddress.sin_port = htons(tport);

    Result = bind(TCPfd, (struct sockaddr *)&ServerAddress, sizeof(ServerAddress));
    if (Result < 0)
    {
        perror("bind() failed");
        close(TCPfd);
        exit(1);
    }

    Result = listen(TCPfd, 32);
    if(0 > Result){
        error("listen failed");
        exit(1);
    }

    bzero((char *) &AuthAddress, sizeof(AuthAddress));
    AuthAddress.sin_family = AF_INET;
    AuthAddress.sin_addr.s_addr = INADDR_BROADCAST;
    AuthAddress.sin_port = htons(authport);

    fds[0].fd = UDPfd;
    fds[0].events = POLLIN | POLLPRI;

    fds[1].fd = TCPfd;
    fds[1].events = POLLIN | POLLPRI;

    fds[2].fd = STDIN_FILENO;
    fds[2].events = POLLIN | POLLPRI;

    timeout = uitimeout;
    SetNonCanonicalMode(STDIN_FILENO, &SavedTermAttributes);
    printf("%llu, %llu\n", P2PI_TRUST_E, P2PI_TRUST_N);
    while(1){       
        diff = time(NULL) - start;

        if((diff >= timeout && getUserNum() <= 0) || restartDiscover){
            start = time(NULL);
            bzero(sendBuffer, sizeof(sendBuffer));
            length = header(sendBuffer, DISCOVERY, uport, tport, username);
            if(!restartDiscover){
                timeout = timeout * 2 < umtimeout ? timeout * 2 : umtimeout;
            }
            printf("Sending discovery, timeout = %ds\n", timeout);
            restartDiscover = 0;
            // DisplayMessage(sendBuffer, length);
            Result = sendto(UDPfd, sendBuffer, length, 0, (struct sockaddr *)&BroadcastAddress, sizeof(BroadcastAddress));
            if(0 > Result){
                error("ERROR send to client");
                break;
            }
            if(!anchorFound){
                printf("Sending authentication request for %s\n", username);
                uint64_t encrypted = SecretNum & 0x00000000FFFFFFFF;
                PublicEncryptDecrypt(encrypted, P2PI_TRUST_E, P2PI_TRUST_N);
                bzero(sendBuffer, sizeof(sendBuffer));
                length = header(sendBuffer, REQAUTH, 0, 0, NULL);
                char buf[8];
                Char64_64Char(buf, encrypted, _64CHAR);
                memcpy(sendBuffer+length, buf, 8);
                //memcpy(sendBuffer+length, encrypted.c, 8);
                length += 8;
                memcpy(sendBuffer+length, username, strlen(username));
                length += strlen(username);
                sendBuffer[length++] = 0;
                DisplayMessage(sendBuffer, length);
                Result = sendto(UDPfd, sendBuffer, length, 0, (struct sockaddr *)&AuthAddress, sizeof(AuthAddress));
                if(0 > Result){
                    error("ERROR send to client");
                    break;
                }
            }
            continue;
        }

        rv = poll(fds, MAX_FD, timeout * 1000);

        if (rv == -1){
            perror("Polling"); 
        } 
        else if (rv == 0){
            continue;
        } 
        else{
            for(int i = 0; i < MAX_FD; i++){
                if(fds[i].revents & POLLIN && i == 0){
                    bzero(recvBuffer, sizeof(recvBuffer));
                    Result = recvfrom(UDPfd, recvBuffer, BUFFER_SIZE, 0, (struct sockaddr *)&ClientAddress, &ClientLength);
                    if(0 > Result){
                        error("ERROR receive from client");
                        break;
                    }
                    int type2 = ntohs(*(uint16_t *)(recvBuffer+4));
                    int uport2, tport2;
		    char *hostname2, *username2;
                    if(type2 == DISCOVERY || type2 == REPLY || type2 == CLOSING){
                        uport2 = ntohs(*(uint16_t *)(recvBuffer+6));
                        tport2 = ntohs(*(uint16_t *)(recvBuffer+8));
                        hostname2 = recvBuffer + 10;
                        username2 = recvBuffer + 10 + strlen(hostname2) + 1;
                    }
                    DisplayMessage(recvBuffer, Result);
                    switch(type2){
                        case DISCOVERY:
                            if(!strcmp(hostname, hostname2) && !strcmp(username, username2)){
                                printf("Receive self discovery\n");
                            }
                            else{
                            	if(!inUserList(username2))
                                    addUser(initUser(uport2, tport2, hostname2, username2));
                            	if(getUserNum() == 1)
                            		printf("Stop broadcasting\n");
                            	printf("Receive discovery from:\n");
                            	printUser(username2);
                                start = time(NULL);
                                bzero(sendBuffer, sizeof(sendBuffer));
                                length = header(sendBuffer, REPLY, uport, tport, username);
                                // DisplayMessage(sendBuffer, length); 
                                Result = sendto(UDPfd, sendBuffer, length, 0, (struct sockaddr *)&ClientAddress, ClientLength);
                                if(0 > Result){
                                    error("ERROR send to client");
                                    break;
                                }
                                // printList();
                            }
                            bzero(recvBuffer, sizeof(recvBuffer));
                            break;
                        case REPLY:
                            // DisplayMessage(recvBuffer, Result);
                            if(!inUserList(username2))
                                addUser(initUser(uport2, tport2, hostname2, username2));
                            if(getUserNum() == 1)
                            	printf("Stop broadcasting\n");
                            printf("Receive reply from:\n");
                            printUser(username2);
                            bzero(recvBuffer, sizeof(recvBuffer));
                            break;
                        case CLOSING:{
                            printf("Receive closing message from '%s'\n", username2);
                            struct User* temp = searchUser(username2);
                            if(temp->TCPfd > 0){
                            	int k = searchFD(temp->TCPfd);
                            	fds[k].fd = -1;
                            	temp->TCPfd = -1;
                            }
                            deleteUser(username2);
                            if(getUserNum() <= 0){
                            	start = time(NULL);
                            	restartDiscover = 1;
                            	timeout = uitimeout;
                            	printf("Resume broadcasting\n");
                            }
                            bzero(recvBuffer, sizeof(recvBuffer));
                            break;
                        }
                        case AUTHREPLY:{
                            printf("HERE!!!!\n");
                            username2 = recvBuffer + 14;
                            Char64_64Char(recvBuffer + 14 + strlen(username2) + 1, PublicKey, _CHAR64);
                            Char64_64Char(recvBuffer + 14 + strlen(username2) + 1 + 8, Modulus, _CHAR64);
                            printf("%llu, %llu\n", PublicKey, Modulus);
                            uint64_t pe;
			    Char64_64Char(recvBuffer + 6, pe, _CHAR64);
                            PublicEncryptDecrypt(pe, P2PI_TRUST_E, P2PI_TRUST_N);
                            printf("%016X\n", pe);
                            break;
                        }
                        default:
                            break;
                    }
                }
                else if(fds[i].revents & POLLIN && i == 1){ 
                    int tempfd = accept(TCPfd, NULL, NULL);
                    if (tempfd < 0){
                        if (errno != EWOULDBLOCK){
                            error("accept() failed");
                        }
                        break;
                    }
                    printf("New incoming connection: %d\n", tempfd);
                    int first = firstAvailableFD();
                    fds[first].fd = tempfd;
                    fds[first].events = POLLIN | POLLPRI;
                }
                else if(fds[i].revents & POLLIN && i == 2){ // STDIN file descriptor
                    read(STDIN_FILENO, &c, 1);
                    if(0x04 == c){
                        break;
                    }
                    else{
                        processCommand(c);
                    }
                }
                else if(fds[i].revents & POLLIN){
                    int j = i-3;
                    int type2 = 0;
                    read(fds[i].fd, messages[j] + msgLen[j], 1);
                    msgLen[j]++;
                    // DisplayMessage(messages[j], msgLen[j]);
                    if(messages[j][msgLen[j]-1] == '\0')
                        zeroCount[j]--;
                    if(msgLen[j] == 6){
                        TCPmsgProcess(j, &fds[i].fd);
                    }
                    else if(msgLen[j] > 6){
                        type2 = ntohs(*(uint16_t *)(messages[j]+4));
                        switch(type2){
                            case ESTABLISH:
                                // DisplayMessage(messages[j], msgLen[j]);
                                if(zeroCount[j] == 0){
                                    printf("Like to connect with %s? (y/n)\n", messages[j]+6);
                                    char ch;
                                    ResetCanonicalMode(STDIN_FILENO, &SavedTermAttributes);
                                    do{
                                        ch = getchar();
                                    }while(ch != 'y' && ch!= 'n' && ch != 'Y' && ch != 'N');
                                    SetNonCanonicalMode(STDIN_FILENO, &SavedTermAttributes);
                                    if(ch == 'y' || ch == 'Y'){
                                        struct User* temp = searchUser(messages[j]+6);
                                        temp->TCPfd = fds[i].fd;
                                        printf("Connection built\n");
                                        bzero(sendBuffer, sizeof(sendBuffer));
                                        length = header(sendBuffer, ACCEPT, 0, 0, NULL);
                                        Result = write(fds[i].fd, sendBuffer, length);
                                        if(0 > Result){
                                            error("ERROR writing to socket");
                                        }
                                        // DisplayMessage(sendBuffer, length);
                                        resetTCPbuf(j);
                                    }
                                    else{
                                        printf("Won't connect\n");
                                        bzero(sendBuffer, sizeof(sendBuffer));
                                        length = header(sendBuffer, UNAVAILABLE, 0, 0, NULL);
                                        Result = write(fds[i].fd, sendBuffer, length);
                                        if(0 > Result){
                                            error("ERROR writing to socket");
                                        }
                                        // DisplayMessage(sendBuffer, length);
                                        resetTCPbuf(j);
                                    }
                                }
                                break;
                            case LISTREPLY:
                                if(msgLen[j] == 10){
                                    int numEntries = ntohl(*(uint32_t *)(messages[j]+6));
                                    zeroCount[j] = 2 * numEntries;
                                    listReplyCount = 10;
                                    listReplySubtype = ENTRY;
                                }
                                else if(msgLen[j] > 10){
				    switch(listReplySubtype){
					case ENTRY:
					    if(messages[j][msgLen[j]-1] == '\0')
						zeroCount[j]++;
					    if(msgLen[j] - listReplyCount == 4){
						printf("ENTRY %d, ", ntohl(*(uint32_t *)(messages[j]+listReplyCount)));
						listReplySubtype = UDPPORT;
						listReplyCount = msgLen[j];
					    }
					    break;
					case UDPPORT:
					    if(messages[j][msgLen[j]-1] == '\0')
						zeroCount[j]++;
					    if(msgLen[j] - listReplyCount == 2){
						printf("UDP port %d, ", ntohs(*(uint16_t *)(messages[j]+listReplyCount)));
						listReplySubtype = HOSTNAME;
						listReplyCount = msgLen[j];
					    }
					    break;
					case HOSTNAME:
					    if(messages[j][msgLen[j]-1] == '\0'){
						char *hostname2 = messages[j] + listReplyCount;
						printf("hostname %s, ", hostname2);
						listReplySubtype = TCPPORT;
						listReplyCount = msgLen[j];
					    }
					    break;
					case TCPPORT:
					    if(messages[j][msgLen[j]-1] == '\0')
						zeroCount[j]++;
					    if(msgLen[j] - listReplyCount == 2){
						printf("TCP port %d, ", ntohs(*(uint16_t *)(messages[j]+listReplyCount)));
						listReplySubtype = USERNAME;
						listReplyCount += 2;
					    }
					    break;
					case USERNAME:
					    if(messages[j][msgLen[j]-1] == '\0'){
						char *username2 = messages[j] + listReplyCount;
						printf("username %s\n", username2);
						if(zeroCount[j] != 0){
						    listReplySubtype = ENTRY;
						    listReplyCount = msgLen[j];
						}
						else
						    resetTCPbuf(j);
						}
					    break;
					default:
					    break;
				    }
                                }
                                break;
                            case DATA:
                                if(zeroCount[j] == 0){
                                	struct User* temp = searchUserByTCP(fds[i].fd);
                                    printf("New message from %s: %s\n", temp->Username, messages[j]+6);
                                    resetTCPbuf(j);
                                }
                                break;
                            default:
                                break;
                        }
                    }
                }
            }
        }
    }
    return 0;  
}  
