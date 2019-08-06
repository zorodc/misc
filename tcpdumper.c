/**
 * \author Daniel Collins
 * This program is licensed under the terms specified in the LICENSE file.
 *
 * A TCP server that writes the contents of successive connections out to a file.
 * Useful for receiving dumps from remote hosts whose files aren't accessible.
 *
 * IPv4 only.
 */

/* C includes */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* Unix includes */
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <errno.h>

#ifndef DEFAULT_PORT_NUMBER
#define PORT_NUMBER 0
#else
#define PORT_NUMBER DEFAULT_PORT_NUMBER
#endif /* DEFAULT_PORT_NUMBER */

#define READ_BUF_SIZE      1024
#define CONNECTION_BACKLOG 32

void errno_panic(void)
{
	printf("PANIC: ", strerror(errno));
	exit(1);
}

ssize_t valid(ssize_t ret)
{
	if (ret < 0) errno_panic();
	else         return ret;
}

struct serv_state
{
	int         sock;
	unsigned    count;
	const char* dump_prefix;
} server = {0, 0, "dump"};

void server_close_sock(void) { valid(close(server.sock)); }
void read_and_dump(struct serv_state* serv, int conn);

int main(int argc, char* argv[]) {
	struct sockaddr_in serv_addr = {
		.sin_family = AF_INET,
		.sin_port   = htons(PORT_NUMBER),
		.sin_addr   = INADDR_ANY
	};

	if (argc > 1) server.dump_prefix = argv[1];
	if (argc > 2) valid(inet_pton(AF_INET, argv[2], &serv_addr.sin_addr));
	if (argc > 3) serv_addr.sin_port = htons((uint16_t)atol(argv[3]));

	server.sock = valid(socket(AF_INET, SOCK_STREAM, IPPROTO_TCP));
	atexit(server_close_sock);

	valid(  bind(server.sock, (void*)&serv_addr, sizeof(serv_addr)));
	valid(listen(server.sock, CONNECTION_BACKLOG));

	int conn;
	while (conn = valid(accept(server.sock, NULL, NULL))) {
		read_and_dump(&server, conn);
		close(conn);
	}

	exit(0);
}

void read_and_dump(struct serv_state* serv, int conn)
{
	char buffer[READ_BUF_SIZE];
	valid(snprintf(buffer, sizeof(buffer), "%s-%u",
	               serv->dump_prefix, serv->count));
	FILE* out = fopen(buffer, "w");
	if (out == NULL) errno_panic();

	++serv->count;
	ssize_t ret;
	while (ret = valid(read(conn, buffer, sizeof(buffer))))
		if (ret == 0) break;
		else fwrite(buffer, ret, 1, out);
	valid(fclose(out));
}
