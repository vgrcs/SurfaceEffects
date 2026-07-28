ROOT := ../..
PROJECT := _CoqProject.smallstep
BUILD := Makefile.smallstep
BUILD_CONF := Makefile.smallstep.conf
BUILD_DEPS := .Makefile.smallstep.d

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
