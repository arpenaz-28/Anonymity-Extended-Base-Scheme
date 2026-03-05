CONTIKI_PROJECT = device-node as-node gw-node
all: $(CONTIKI_PROJECT)

CONTIKI = ../..
PROJECT_SOURCEFILES += aes.c sha256.c
MODULES += os/net/app-layer/coap

# Suppress errors for unused variables and functions
CFLAGS += -Wno-error=unused-function
CFLAGS += -Wno-error=unused-variable
CFLAGS += -Wno-error=unused-result
CFLAGS += -Wno-error=unused-but-set-variable

include $(CONTIKI)/Makefile.include
