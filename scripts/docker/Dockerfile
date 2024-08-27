# Intructions on how to build jasmin-leakage-free image (from the jasmin-leakage-freeness/scripts/docker directory):
# $ docker build -t jasmin-leakage-free:latest -f Dockerfile ../../
# $ docker run --rm -it jasmin-leakage-free
# $ make -j$(nproc)
# $ make compile_and_run
# $ exit

# Notes:
# - the command `make` checks the proofs; using 8 cores (assuming modern desktop CPU) it is expected that checking the proofs takes around 1.5 minutes to complete; Note: to run the all proofs again (without modifying the EasyCrypt files), you can run `make ec_clean`.
# - the command `make compile_and_run` compiles and runs the example code
# - the command `exit` exits the docker container; because flag `--rm` was provided to `docker run`, it is expected that the container is removed after exiting

# Some more notes about Docker to help the user of this Dockerfile:
# - Using Docker, and in particular this Dockerfile given its dependencies, requires some free disk space (around 4 to 5GB).
# - As such, it is important to keep things clean. You can check Docker disk usage with the command `docker system df`.
# - With the command `docker ps -a` you can check existing containers: with `docker rm 'CONTAINER ID'` or `docker rm 'NAME'` you can remove containers.
#   * if the container is still running, you need to stop it before attempting removal with the previous commands.
#   * this can be done with `docker stop 'CONTAINER ID'` or `docker stop 'NAME'`.
# - With the command `docker image ls` you can check the existing images on your system and then with `docker image rm 'REPOSITORY'` or `docker image rm 'IMAGE ID'` removes the corresponding image.
# - The command `docker system prune` is helpful for performing a general system cleanup (it is expected that the command prints a message describing what it will do and asks for user confirmation).
#   * When given option `-a` to `prune`, as in `docker system prune -a`, the cleaning process is more thorough (a message is also printed). 

FROM debian:stable-20240812-slim

ARG USER=jasminlf

# gitlab://https.com/jasmin-lang/jasmin-compiler/-/tree/v2024.07.0
ARG JASMIN_RELEASE=v2023.06.4
ARG EASYCRYPT_COMMIT=a214a56

SHELL ["/bin/bash", "-c"]
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get --quiet --assume-yes update && \
    apt-get --quiet --assume-yes upgrade && \
    apt-get --quiet --assume-yes install apt-utils && \
    apt-get --quiet --assume-yes install \
      sudo wget curl git time xz-utils libicu-dev \
      ocaml ocaml-native-compilers camlp4-extra opam \
      autoconf debianutils libgmp-dev pkg-config zlib1g-dev \
      vim build-essential python3 python3-pip m4 libgsl-dev \ 
      libpcre3-dev jq parallel valgrind bash-completion \
      libtext-diff-perl

RUN apt-get --quiet --assume-yes clean

RUN echo "%sudo  ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers.d/sudoers && \
    chown root:root /etc/sudoers.d/sudoers && \
    chmod 0400 /etc/sudoers.d/sudoers && \
    useradd --create-home --shell /bin/bash --home-dir /home/$USER --user-group --groups sudo --uid 1001 $USER

USER $USER
WORKDIR /home/$USER

RUN curl -L https://nixos.org/nix/install > nix-install && \
    sh nix-install

# jasmin ######################################################################

RUN wget https://github.com/jasmin-lang/jasmin/releases/download/$JASMIN_RELEASE/jasmin-compiler-$JASMIN_RELEASE.tar.bz2 && \
    tar -xf jasmin-compiler-$JASMIN_RELEASE.tar.bz2 && \
    cd jasmin-compiler-$JASMIN_RELEASE/compiler/ && \
    USER=$USER source /home/$USER/.nix-profile/etc/profile.d/nix.sh && \
    nix-channel --update && \
    nix-shell --command "make" && \
    sudo install -D jasminc /usr/local/bin/ && \
    sudo install -D jasmin-ct /usr/local/bin/

# easycrypt ###################################################################

# alt-ergo 2.4.2
RUN export OPAMYES=true OPAMVERBOSE=0 OPAMJOBS=$(nproc) && \
    opam init --disable-sandboxing && \
    opam install opam-depext && \
    opam pin add -n alt-ergo 2.4.2 && \
    opam install alt-ergo && \
    opam clean

# cvc4 1.8
RUN wget --no-verbose --show-progress --progress=bar:force:noscroll --timeout=10 --waitretry=5 --tries=5 \
      -O cvc4 https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-x86_64-linux-opt && \ 
    sudo install -D cvc4 /usr/local/bin/
    
# z3 4.8.7
RUN wget --no-verbose --show-progress --progress=bar:force:noscroll --timeout=10 --waitretry=5 --tries=5 \
      https://github.com/Z3Prover/z3/releases/download/z3-4.8.7/z3-4.8.7-x64-ubuntu-16.04.zip && \
    unzip -j z3-4.8.7-x64-ubuntu-16.04.zip z3-4.8.7-x64-ubuntu-16.04/bin/z3 && \
    sudo install -D z3 /usr/local/bin/

# easycrypt
RUN eval $(opam env) && \
    export OPAMYES=true OPAMVERBOSE=0 OPAMJOBS=$(nproc) && \
    opam pin -n add easycrypt https://github.com/EasyCrypt/easycrypt.git#$EASYCRYPT_COMMIT && \
    opam depext easycrypt && \
    opam install easycrypt && \
    easycrypt why3config

# jasmin-leakage-free ###############################################################

COPY --chown=$USER:$USER . /home/$USER/jasmin-leakage-free
WORKDIR /home/$USER/jasmin-leakage-free

# starting point ####################################################################
RUN echo 'eval $(opam env)' >> /home/$USER/.bashrc
CMD ["bash"]

