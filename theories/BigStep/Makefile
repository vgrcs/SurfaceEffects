ROOT := ../..
PROJECT := _CoqProject.bigstep
BUILD := Makefile.bigstep
BUILD_CONF := Makefile.bigstep.conf
BUILD_DEPS := .Makefile.bigstep.d

.PHONY: all build clean distclean

all: build

build:
	cd $(ROOT) && rocq makefile -f $(PROJECT) -o $(BUILD)
	$(MAKE) -C $(ROOT) -f $(BUILD) real-all

clean:
	@if [ -f "$(ROOT)/$(BUILD)" ]; then \
		$(MAKE) -C $(ROOT) -f $(BUILD) clean; \
	fi

distclean: clean
	rm -f $(ROOT)/$(BUILD) $(ROOT)/$(BUILD_CONF) $(ROOT)/$(BUILD_DEPS)
