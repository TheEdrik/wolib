#!/usr/bin/python3

# retrieve incrementally-improving logs from a number of clients
# output global optimum across all clients
#
# results are reported in consecutive non-whitespace lines
# 'best' result is extracted by a reg.expression (reBEST below)
# each new then-best result is reported further to a downstream server
#
# assume input is in blank/all-whitespace-separated records
# TODO: we use record bytecount as cost in this demo version
# TODO: fetch full record (only tested with all-delivering localhost!)
#
# set TARGET=...server...:...port..., or use 'vSERVER' as default


# TODO: pick from env
# port forward from PRTI to PRTO
#
vPORTin      = 8000
vPORTout     = 9000
vCLIENTS_MAX = 100
#
vSERVER = 'localhost'             ## server to forward to
vHOST   = 'localhost'

# worst-case size
vMSGBYTES = 100000

# separator (telnet)
vCRLF = b'\r\n'


##============================================================================
import socketserver, socket, os, threading, re


##----
gTGTSOCKET = None          ## socket to server, shared
gBEST      = -1            ## optimum so far
##
gTLOCK = threading.Lock()
gBLOCK = threading.Lock()


##--------------------------------------
## iterator: return one record with each iteration
##
## TODO: proper stream de/parsing would come here
##
def records(raw):
	lines = [ re.sub(b'^\s+$', '', rec)  for rec in raw.split(vCRLF) ]
				## collapse all-whitespace lines

	## TODO: list comprehension with full expression

	res, regions, lastcrlf = [], [], False
				## regions stores (offset, elem.count)
				## for each net region

	for ri, r in enumerate(lines):
		if (r != b''):
			if (ri == 0) or lastcrlf:
				regions.append([ ri, 0 ])

			regions[-1][1] += 1                          ## +1 line
			res.append(r)
			lastcrlf = False
			continue

		if (res != []) and (not lastcrlf):
			res.append(r)

		lastcrlf = True

	for rx in regions:
		roffs, rcount = rx[0], rx[1]
		yield vCRLF.join(lines[ roffs : roffs+rcount ])


##--------------------------------------
## register new input
## returns None if result does not improve result; non-None otherwise
##
def register1(record):
	global gBEST

	rv = None
	gBLOCK.acquire()

	if len(record) > gBEST:
		gBEST = len(record)
		rv = gBEST

	gBLOCK.release()
	return rv


##--------------------------------------
## pass through record to server
##
def passthrough1(record):
	if gTGTSOCKET:
		gTLOCK.acquire()

		gTGTSOCKET.send(record)
		gTGTSOCKET.send(vCRLF +vCRLF)

		gTLOCK.release()


##--------------------------------------
## connect to server, or fail with None
##
## returns (server name), (socket) pair
##
def socket_open(target, port):
	try:
		if 'TARGET' in os.environ:
			target = os.environ[ 'TARGET' ]

		s = socket.socket()
		s.connect((target, port))
	except:
		s = None                               ## TODO: error reporting

	return target, s


##---------------------------------------------------
class collector(socketserver.BaseRequestHandler):
	"""one collector-request handler"""

				# self.request is TCP socket from client
	def handle(self):
		rd = self.request.recv(vMSGBYTES)

		for curr in records(rd):
			if register1(curr) != None:
				passthrough1(curr)

		self.request.sendall(b'abc\n')


##---------------------------------------------------
if __name__ == "__main__":
	tgt, gTGTSOCKET = socket_open(vSERVER, vPORTout)
	if (gTGTSOCKET == None):
		raise ValueError(f"can not connect to server ({tgt})")

	with socketserver.TCPServer((vHOST, vPORTin), collector) as server:
		server.serve_forever()

