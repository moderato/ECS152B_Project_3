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
#include <arpa/inet.h>
#include "userlist.h"
#include "EncryptionLibrary.h"
#include "helper.h"

#define BUFFER_SIZE 512
#define MAX_FD      50
#define _64CHAR     0
#define _CHAR64     1
#define SPECSOCKNUM 3

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
#define INPUTMSG    0x0003
#define TODELETE    0x0004
#define TODISCON    0x0005
#define TOREQUEST   0x0006
#define ESTBAUTH    0x0007

const char* short_options = "p:h:";  
int UDPfd, TCPfd; // UDP and TCP server sockets
int TCPs[MAX_FD-SPECSOCKNUM], msgLen[MAX_FD-SPECSOCKNUM], zeroCount[MAX_FD-SPECSOCKNUM], dummyCount[MAX_FD-SPECSOCKNUM]; // For each user
char messages[MAX_FD-SPECSOCKNUM][BUFFER_SIZE], decMessages[MAX_FD-SPECSOCKNUM][BUFFER_SIZE]; // For each user
char hostname[256]; //Defined as extern in helper.h
char *username;
int uport = 50550, tport = 50551, authport = 50552, uitimeout = 5, umtimeout = 60; // For this machine
int nonCanState = NORMAL; // Non-canonical mode state
int anchorFound = 0; // If a trust anchor is found
struct sockaddr_in AuthAddress, BroadcastAddress, UserAddress; // For authentication, broadcasting and sending tcp
struct termios SavedTermAttributes; // For non canonical mode
struct pollfd fds[MAX_FD]; // Polling structures
struct User* activeUser = NULL; // Who are we talking to
char nonCanBuffer[BUFFER_SIZE]; // Buffer non-canonical mode input
int nonCanLength = 0; // Length of the buffered message
uint64_t SecretNum, PublicKey, Modulus, PrivateKey;


// All local buffers in functions are called buf

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
    int length = prepareHeader(buf, CLOSING, uport, tport, username);
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

// Authenticate a user
void authenticate(char* user){
    char sendBuffer[BUFFER_SIZE], buf[8];
	printf("Sending authentication request for %s\n", user);
	uint64_t encrypted = SecretNum & 0x00000000FFFFFFFF;
	PublicEncryptDecrypt(encrypted, P2PI_TRUST_E, P2PI_TRUST_N);
	bzero(sendBuffer, sizeof(sendBuffer));
	int length = prepareHeader(sendBuffer, REQAUTH, 0, 0, NULL);
	bzero(buf, sizeof(buf));
	Char64_64Char(buf, encrypted, _64CHAR);
	memcpy(sendBuffer+length, buf, 8);
	length += 8;
	memcpy(sendBuffer+length, user, strlen(user));
	length += strlen(user);
	sendBuffer[length++] = 0;
	// DisplayMessage(sendBuffer, length);
	int Result = sendto(UDPfd, sendBuffer, length, 0, (struct sockaddr *)&AuthAddress, sizeof(AuthAddress));       
	if(0 > Result){
		error("ERROR send to client");
		exit(1);
	}
}

void processCommand(char c){
    if(nonCanState == NORMAL){
		switch(c){
			case 'H': case 'h':
				printf("\nHelp:\n");
				printf("    C/c: Connect to a user in list\n");
				printf("    D/d: Delete a user in list\n");
				printf("    E/e: Connect to a user in list (encrypted)\n");
				printf("    S/s: Speak to a user in list\n");
				printf("    Q/q: Disconnect a user in list\n");
				printf("    L/l: List users\n");
				printf("    R/r: Request User List\n");
				printf("    I/i: See info for this machine\n\n");
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
			case 'E': case 'e': // Build encrypted connection with a user
				if(getUserNum() != 0){
					printf("Which one to establish encrypted connection? Input a number:\n");
					nonCanState = ESTBAUTH;
				}
				else{
					printf("No user to connect\n");
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
			case 'Q': case 'q': // Disconnect a user
				if(getUserNum() != 0){
					printf("Which one to disconnect? Input a number:\n");
					nonCanState = TODISCON;
				}
				else{
					printf("No user to disconnect\n");
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
			case ESTBAUTH:
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
					if(nonCanState == ESTBAUTH && temp->Authenticated == 0){
                        printf("%s is not authenticated!\n", temp->Username);
                        authenticate(temp->Username);
                    }
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
						int first = firstAvailableFD(fds);
						fds[first].fd = temp->TCPfd;
						fds[first].events = POLLIN | POLLPRI;
						char buf[BUFFER_SIZE];
						int length;
						if(nonCanState == TOCONNECT){
						    if(temp->Authenticated == 1){
                                memcpy(buf, temp->Username, strlen(temp->Username));
                                length = strlen(temp->Username) + 1;
						        prepareEncrMsg(ESTABLISH, buf, length, temp->Username);
						    }
						    else
							    length = prepareHeader(buf, ESTABLISH, 0, 0, temp->Username);
					    }
						if(nonCanState == ESTBAUTH){
							length = prepareHeader(buf, ESTABCRYPT, 0, 0, temp->Username);
							char tmp[8];
							Char64_64Char(tmp, PublicKey, _64CHAR);
							memcpy(buf+length, tmp, 8);
							length += 8;
							Char64_64Char(tmp, Modulus, _64CHAR);
							memcpy(buf+length, tmp, 8);
							length += 8;
						}
						// DisplayMessage(buf, length);
						int Result = write(temp->TCPfd, buf, length);
						if(0 > Result){
							error("ERROR writing to socket");
						}
						printf("Waiting for reply...\n");
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
					int length;
					bzero(buf, BUFFER_SIZE);
					if(activeUser->Authenticated == 1){
					    length = strlen(nonCanBuffer);
					    memcpy(buf, nonCanBuffer, length++);
					    prepareEncrMsg(DATA, buf, length, activeUser->Username);
					}
					else{
					    length = prepareHeader(buf, DATA, 0, 0, NULL);
					    memcpy(buf+length, nonCanBuffer, strlen(nonCanBuffer));
					    length += strlen(nonCanBuffer) + 1;
					}
					// DisplayMessage(buf, length);
					int Result = write(activeUser->TCPfd, buf, length);
					if(0 > Result){
						error("ERROR writing to socket");
					}
					printf("Message sent: %s\n", nonCanBuffer);
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
			case TODISCON:
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
						printf("Already disconnected\n");
					}
					else{
						char buf[BUFFER_SIZE];
						int length = 0;
						if(temp->Authenticated == 1){
						    prepareEncrMsg(DISCONTINUE, buf, length, temp->Username);
						}
						else
						    length = prepareHeader(buf, DISCONTINUE, 0, 0, NULL);
						// DisplayMessage(buf, length);
						int Result = write(temp->TCPfd, buf, length);
						if(0 > Result){
							error("ERROR writing to socket");
						}
						int i = searchFD(temp->TCPfd, fds);
						temp->TCPfd = -1;
						fds[i].fd = -1;
						printf("User %s's connection closed\n", temp->Username);
					}
					temp->SequenceNum[0] = 0;
					temp->SequenceNum[1] = 0;
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
						int length = 0;
						if(temp->Authenticated == 1)
						    prepareEncrMsg(USERLIST, buf, length, temp->Username);
						else
						    length = prepareHeader(buf, USERLIST, 0, 0, NULL);
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
}

int main(int argc, char *argv[])
{
    int Result, rv, c, length;
    char recvBuffer[BUFFER_SIZE], sendBuffer[BUFFER_SIZE], password[BUFFER_SIZE], buf[8];
    struct sockaddr_in ServerAddress, ClientAddress;
    socklen_t ClientLength = sizeof(ClientAddress);
    int broadcast = 1, on = 1;
    int timeout = 0, restartDiscover = 1;
    time_t start = time(NULL), diff;
    uint64_t encrypted;

    if(-1 == gethostname(hostname, 255)){
        error("No host name.\n");
        exit(1);
    }
    username = getenv("USER");
    memset(msgLen, 0, MAX_FD-SPECSOCKNUM);
    memset(zeroCount, 0, MAX_FD-SPECSOCKNUM);
    memset(dummyCount, 0, MAX_FD-SPECSOCKNUM);
    SecretNum = GenerateRandomValue();
    printf("Enter password for %s> ", username);
    fgets(password, sizeof(password), stdin);
    char usr_pwd[BUFFER_SIZE];
    bzero(usr_pwd, sizeof(usr_pwd));
    memcpy(usr_pwd, username, strlen(username));
    usr_pwd[strlen(username)] = ':';
    memcpy(usr_pwd+strlen(username)+1, password, strlen(password));
    usr_pwd[strlen(usr_pwd)-1] = 0;
    uint64_t n,e,d;
    DisplayMessage(usr_pwd, strlen(usr_pwd));
    printf("%s\n", usr_pwd);
    StringToPublicNED(usr_pwd, n, e, d);
    printf("%llu, %llu, % llu\n", n, e, d);

    char* pch = NULL;
    char* trustHost;
    int trustPort = 0;
    
    while((c = getopt_long(argc, argv, short_options, long_options, NULL)) != -1){  
        switch (c)  
        {  
            case 'p':
                authport = atoi(optarg);
                break;
            case 'h':
                printf("%s\n", optarg);
                trustHost = strtok(optarg, ":");
                if(trustHost != NULL){
                    printf("%s\n", trustHost);
                    pch = strtok(NULL, ":");
                    if(NULL != pch)
                        trustPort = atoi(pch);
                    if(trustPort > 0)
                        authport = trustPort;
                    printf("%d\n", authport);
                }
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
    signal(SIGSEGV, SignalHandler);

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
    AuthAddress.sin_port = htons(authport);
    if(trustHost != NULL){
        struct hostent* Trust = gethostbyname(trustHost);
        if(NULL == Trust){
	        fprintf(stderr,"ERROR, no such host\n");
	        printf("Still use broadcasting\n");
	        AuthAddress.sin_addr.s_addr = INADDR_BROADCAST;
	        printf("%s\n", inet_ntoa(AuthAddress.sin_addr));
        }
        else{
            bcopy((char *)Trust->h_addr, (char *)&AuthAddress.sin_addr.s_addr, Trust->h_length);
            printf("Specify trust anchor as port %d at hostname %s\n", authport, trustHost);
            printf("%s\n", inet_ntoa(AuthAddress.sin_addr));
        }
    }
    else
        AuthAddress.sin_addr.s_addr = INADDR_BROADCAST;
    
    fds[0].fd = UDPfd;
    fds[0].events = POLLIN | POLLPRI;

    fds[1].fd = TCPfd;
    fds[1].events = POLLIN | POLLPRI;

    fds[2].fd = STDIN_FILENO;
    fds[2].events = POLLIN | POLLPRI;

    timeout = uitimeout;
    SetNonCanonicalMode(STDIN_FILENO, &SavedTermAttributes);
    while(1){       
        diff = time(NULL) - start;

        if((diff >= timeout && getUserNum() <= 0) || restartDiscover){
            start = time(NULL);
            bzero(sendBuffer, sizeof(sendBuffer));
            length = prepareHeader(sendBuffer, DISCOVERY, uport, tport, username);
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
                authenticate(username);
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
					struct User* temp;
                    if(type2 == DISCOVERY || type2 == REPLY || type2 == CLOSING){
                        uport2 = ntohs(*(uint16_t *)(recvBuffer+6));
                        tport2 = ntohs(*(uint16_t *)(recvBuffer+8));
                        hostname2 = recvBuffer + 10;
                        username2 = recvBuffer + 10 + strlen(hostname2) + 1;
                        temp = searchUser(username2);
                    }
                    // DisplayMessage(recvBuffer, Result);
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
								printf("Receive discovery from %s\n", username2);
                                if(anchorFound)
                                    authenticate(username2);
                                start = time(NULL);
                                bzero(sendBuffer, sizeof(sendBuffer));
                                length = prepareHeader(sendBuffer, REPLY, uport, tport, username);
                                // DisplayMessage(sendBuffer, length); 
                                Result = sendto(UDPfd, sendBuffer, length, 0, (struct sockaddr *)&ClientAddress, ClientLength);
                                if(0 > Result){
                                    error("ERROR send to client");
                                    break;
                                }
                            }
                            break;
                        case REPLY:
                            if(!inUserList(username2))
                                addUser(initUser(uport2, tport2, hostname2, username2));
                            if(getUserNum() == 1)
								printf("Stop broadcasting\n");
                            printf("Receive reply from %s\n", username2);
                            if(anchorFound)
                                authenticate(username2);
                            break;
                        case CLOSING:{
                            printf("Receive closing message from '%s'\n", username2);
                            deleteUser(username2);
                            if(getUserNum() <= 0){
								start = time(NULL);
								restartDiscover = 1;
								timeout = uitimeout;
								printf("Resume broadcasting\n");
                            }
                            break;
                        }
                        case AUTHREPLY:{
                            username2 = recvBuffer + 14;
                            if(!anchorFound){ // Authenticate myself
								Char64_64Char(recvBuffer + 14 + strlen(username2) + 1, PublicKey, _CHAR64);
								Char64_64Char(recvBuffer + 14 + strlen(username2) + 1 + 8, Modulus, _CHAR64);
								// printf("%llu, %llu\n", PublicKey, Modulus);
								if(e == PublicKey && n == Modulus){
                                    // printf("%llu, %llu\n", PublicKey, Modulus);
									printf("Password authenticated, trust anchor found\n", username);
									bzero((char *)&AuthAddress, sizeof(AuthAddress));
									memcpy((char *)&AuthAddress, (char *)&ClientAddress, sizeof(ClientAddress));
									anchorFound = 1;
									PrivateKey = d;
								}
								else{
									printf("Authentication Failed!\n");
									// exit(0);
								}
								break;
                            }
                            else{
                                uint64_t pk, mdl;
                                Char64_64Char(recvBuffer + 14 + strlen(username2) + 1, pk, _CHAR64);
                                Char64_64Char(recvBuffer + 14 + strlen(username2) + 1 + 8, mdl, _CHAR64);
                                temp = searchUser(username2);
                                if(temp == NULL){
                                    if(!strcmp(username2, username))
                                        printf("Omit duplicate authentication reply\n");
                                    else
                                        printf("No user named %s\n", username2);
                                }
                                else if(pk > 0 && mdl > 0){
                                    printf("User %s authenticated\n", username2);
                                    temp->Authenticated = 1;
                                }
                                else{
									printf("User %s unauthenticated\n", username2);
									temp->Authenticated = 0;
                                }
                            }
                            break;
                        }
                        default:
                            break;
                    }
                    bzero(recvBuffer, sizeof(recvBuffer));
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
                    int first = firstAvailableFD(fds);
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
                    int j = i-SPECSOCKNUM;
                    uint16_t type2 = 0;
                    read(fds[i].fd, messages[j] + msgLen[j], 1);
                    msgLen[j]++;
                    // DisplayMessage(messages[j], msgLen[j]);
                    if(msgLen[j] >= 6){
                        type2 = ntohs(*(uint16_t *)(messages[j]+4));
                        switch(type2){
                            case ACCEPT:
                                printf("Connection accepted!\n");
                                resetTCPbuf(j);
                                break;
                            case UNAVAILABLE:{
                                struct User* temp = searchUserByTCP(fds[i].fd);
                                temp->TCPfd = -1;
                                printf("Connection unavailable\n");
                                resetTCPbuf(j);
                            }
                                break;
                            case USERLIST:
                                bzero(sendBuffer, sizeof(sendBuffer));
                                length = prepareHeader(sendBuffer, LISTREPLY, 0, 0, NULL);
                                prepareListReply(sendBuffer, length);
                                // DisplayMessage(sendBuffer, length);
                                Result = write(fds[i].fd, sendBuffer, length);
                                if(0 > Result){
	                                error("ERROR writing to socket");
                                }
                                printf("User list sent!\n");
                                resetTCPbuf(j);
                                break;
                            case DISCONTINUE:{
                                printf("Receive discontinue from fd %d\n", fds[i].fd);
                                struct User* temp = searchUserByTCP(fds[i].fd);
                                fds[i].fd = -1;
                                temp->TCPfd = -1;
                                resetTCPbuf(j);
                            }
                                break;
                            case ESTABLISH:
                                // DisplayMessage(messages[j], msgLen[j]);
                                if(msgLen[j] > 0 && msgLen[j] <= BUFFER_SIZE && messages[j][msgLen[j]-1] == 0){
                                    printf("Like to connect with %s? (y/n)\n", messages[j]+6);
                                    char ch;
                                    ResetCanonicalMode(STDIN_FILENO, &SavedTermAttributes);
                                    do{
                                        ch = getchar();
                                    }while(ch != 'y' && ch!= 'n' && ch != 'Y' && ch != 'N');
                                    SetNonCanonicalMode(STDIN_FILENO, &SavedTermAttributes);
                                    struct User* temp = searchUser(messages[j]+6);
                                    if(ch == 'y' || ch == 'Y'){
                                        temp->TCPfd = fds[i].fd;
                                        printf("Connection built\n");
                                        bzero(sendBuffer, sizeof(sendBuffer));
                                        length = prepareHeader(sendBuffer, ACCEPT, 0, 0, NULL);
                                        Result = write(fds[i].fd, sendBuffer, length);
                                        if(0 > Result){
                                            error("ERROR writing to socket");
                                        }
                                        resetTCPbuf(j);
                                    }
                                    else{
                                        printf("Won't connect\n");
                                        bzero(sendBuffer, sizeof(sendBuffer));
                                        length = prepareHeader(sendBuffer, UNAVAILABLE, 0, 0, NULL);
                                        Result = write(fds[i].fd, sendBuffer, length);
                                        if(0 > Result){
                                            error("ERROR writing to socket");
                                        }
                                        temp->TCPfd = -1;
                                        resetTCPbuf(j);
                                    }
                                }
                                break;
                            case ESTABCRYPT:{
                                // DisplayMessage(messages[j], msgLen[j]);
                                if(!(msgLen[j] == 6 + strlen(messages[j] + 6) + 1 + 16))
                                    break;
                                printf("Receive establish encryption connection message!\n");
                                struct User* temp = searchUser(messages[j]+6);
                                // temp->TCPfd = -1;
                                temp->TCPfd = fds[i].fd;
                                uint64_t tmpKey, tmpMod;
								Char64_64Char(messages[j] + msgLen[j]-16, tmpKey, _CHAR64);
								Char64_64Char(messages[j] + msgLen[j]-8, tmpMod, _CHAR64);
								if(anchorFound){ // Authenticate this user
									authenticate(messages[j]+6);
								}
                                bzero(sendBuffer, sizeof(sendBuffer));
								length = prepareHeader(sendBuffer, ACCPTCRYPT, 0, 0, temp->Username);
								temp->SequenceNum[0] = GenerateRandomValue();
								temp->SequenceNum[1] = temp->SequenceNum[0];
								uint64_t tmp = temp->SequenceNum[0] >> 32;
								PublicEncryptDecrypt(tmp, tmpKey, tmpMod);
								bzero(buf, sizeof(buf));
								Char64_64Char(buf, tmp, _64CHAR);
								memcpy(sendBuffer+length, buf, 8);
								length += 8;
								tmp = temp->SequenceNum[0] & 0x00000000FFFFFFFF;
								PublicEncryptDecrypt(tmp, tmpKey, tmpMod);
								Char64_64Char(buf, tmp, _64CHAR);
								memcpy(sendBuffer+length, buf, 8);
								length += 8;
								// DisplayMessage(sendBuffer, length);
                                Result = write(fds[i].fd, sendBuffer, length);
                                if(0 > Result){
                                    error("ERROR writing to socket");
                                }
                                resetTCPbuf(j);
                            }
                                break;
                            case LISTREPLY:
                                if(msgLen[j] >= 10){
                                    if(msgLen[j] > 0 && msgLen[j] <= BUFFER_SIZE && messages[j][msgLen[j]-1] != '\0')
                                        break;
                                    processListReply(j, messages[j]+4, msgLen[j]-4);
                                }
                                break;
                            case DATA:
                                if(msgLen[j] > 0 && msgLen[j] <= BUFFER_SIZE && messages[j][msgLen[j]-1] == 0){
									struct User* temp = searchUserByTCP(fds[i].fd);
                                    printf("New message from %s: %s\n", temp->Username, messages[j]+6);
                                    resetTCPbuf(j);
                                }
                                break;
                            case ACCPTCRYPT:
                                if(msgLen[j] == 22){
                                    // DisplayMessage(messages[j], msgLen[j]);
                                    struct User* temp = searchUserByTCP(fds[i].fd);
                                    uint64_t tmp;
                                    Char64_64Char(messages[j]+6, tmp, _CHAR64);
                                    PublicEncryptDecrypt(tmp, PrivateKey, Modulus);
                                    temp->SequenceNum[0] = tmp << 32;
                                    Char64_64Char(messages[j]+14, tmp, _CHAR64);
                                    PublicEncryptDecrypt(tmp, PrivateKey, Modulus);
                                    temp->SequenceNum[0] += tmp & 0x00000000FFFFFFFF;
                                    temp->SequenceNum[1] = temp->SequenceNum[0];
                                    printf("Got sequence number!\n");
                                    // temp->TCPfd = -1;
                                    temp->isRequestor = 1;
                                    resetTCPbuf(j);
                                }
                                break;
                            case DATACRYPT:
                                if(msgLen[j] % 70 == 0){
                                    // DisplayMessage(messages[j], msgLen[j]);
                                    char buf[64];
                                    memcpy(buf, messages[j] + 6 + msgLen[j] - 70, 64);
                                    struct User* temp = searchUserByTCP(fds[i].fd);
                                    temp->SequenceNum[!temp->isRequestor] += !temp->isRequestor ? 1 : -1;
                                    PrivateEncryptDecrypt((uint8_t *)buf, 64, temp->SequenceNum[!temp->isRequestor]);
                                    // DisplayMessage(buf, 64);
                                    uint16_t type3 = ntohs(*(uint16_t *)buf);
                                    if(type3 == EncrTypes[DUMMY]){
                                        printf("Dummy chunk, abandon\n");
                                        bzero(buf, 64);
                                        dummyCount[j]++;
                                        break;
                                    }
                                    int actualLen;
                                    actualLen = 64 * (msgLen[j] / 70 - dummyCount[j]);
                                    memcpy(decMessages[j] + actualLen - 64, buf, 64);
                                    // DisplayMessage(decMessages[j], actualLen);
                                    type3 = ntohs(*(uint16_t *)(decMessages[j]));
                                    switch(type3){
                                        case EncrTypes[USERLIST]:
                                            bzero(sendBuffer, sizeof(sendBuffer));
                                            length = 0;
                                            prepareListReply(sendBuffer, length);
                                            prepareEncrMsg(LISTREPLY, sendBuffer, length, temp->Username);
                                            // DisplayMessage(sendBuffer, length);
                                            Result = write(fds[i].fd, sendBuffer, length);
                                            if(0 > Result){
                                                error("ERROR writing to socket");
                                            }
                                            printf("User list sent!\n");
                                            resetTCPbuf(j);
                                            break;
                                        case EncrTypes[DATA]:{
                                            int index = 0;
                                            while(index < actualLen)
                                                if(decMessages[j][index++] == '\0')
                                                    break;
                                            if(index == actualLen)
                                                break;
                                            else{
                                                printf("New message from %s: %s\n", temp->Username, decMessages[j]+2);
                                                resetTCPbuf(j);
                                            }
                                        }
                                            break;
                                        case EncrTypes[LISTREPLY]:
                                            // DisplayMessage(decMessages[j], actualLen);
                                            processListReply(j, decMessages[j], actualLen);
                                            break;
                                        case EncrTypes[DISCONTINUE]:
                                            printf("Receive discontinue from fd %d\n", fds[i].fd);
                                            fds[i].fd = -1;
                                            temp->TCPfd = -1;
                                            temp->SequenceNum[0] = 0;
                                            temp->SequenceNum[1] = 0;
                                            resetTCPbuf(j);
                                            break;
                                        default:
                                            break;
                                    }                                   
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
