#===- lib/safestack/Makefile.mk ------------------------------*- Makefile -*--===#
#
#                     The LLVM Compiler Infrastructure
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#

ModuleName := safestack
SubDirs :=

Sources := $(foreach file,$(wildcard $(Dir)/*.cc),$(notdir $(file)))
ObjNames := $(Sources:%.cc=%.o)

Implementation := Generic

# FIXME: use automatic dependencies?
Dependencies := $(wildcard $(Dir)/*.h)
Dependencies += $(wildcard $(Dir)/../interception/*.h)

# Define a convenience variable for all the safestack functions.
SafeStackFunctions := $(Sources:%.cc=%)
