{
  description = "A Flake for Perennial development, with Goose and Grackle";

  inputs = {
    nixpkgs.url = "nixpkgs";
    opam-nix.url = "github:tweag/opam-nix";
    opam-repository.url = "github:ocaml/opam-repository";
    opam-repository.flake = false;
    opam-coq-repository.url = "github:coq/opam-coq-archive";
    opam-coq-repository.flake = false;
    nix-vscode-extensions.url = "github:nix-community/nix-vscode-extensions";
  };

  outputs = {
    nixpkgs,
    flake-utils,
    grackle,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
      in {
        devShells.default = with pkgs;
          mkShell {
            buildInputs = [
              coq
              coqPackages.stdlib

              go
              grackle.packages.${system}.default
              grackle.packages.${system}.goose
              protobuf

              # nix helpers
              nix-prefetch-git
              nix-prefetch-github
              nix-prefetch
            ];

            shellHook = ''
              unset COQPATH
            '';
          };
      }
    );
}
