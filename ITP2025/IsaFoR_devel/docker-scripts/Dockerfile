FROM alpine
LABEL description="Builds API static binary"

# install ghc, sources
RUN apk update && apk upgrade
RUN apk add alpine-sdk git linux-headers ca-certificates gmp-dev zlib-dev ghc curl expat-dev expat-static
