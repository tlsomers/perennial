{
  description = "A Flake for Perennial development, with Goose and Grackle";

  inputs = {
    nixpkgs.url = "nixpkgs";
    nix-vscode-extensions.url = "github:nix-community/nix-vscode-extensions";
  };

  outputs = {nixpkgs, ...}@inputs: let
    system = "x86_64-linux";
    codium_settings = ./codium-settings.json;
  in {
    devShells."${system}".default = let
      pkgs = import nixpkgs {
        inherit system;
        config.allowUnfree = true;
      };
      grackle = pkgs.buildGoModule {
        name = "grackle";
        src = pkgs.fetchFromGitHub {
          owner = "mjschwenne";
          repo = "grackle";
          rev = "3a83c3b22f163da77d75bfdb3923f007af2ad515";
          sha256 = "1bl8lx50qhl6yczjnwfwywx29nvinr20v2zjdc2zjqi8kcls7kqr";
        };
        vendorHash = "sha256-c9+npmcdynfqSnxEZSdubVeN8Y3eYAwjya52vTJayY0=";
        checkPhase = false;
      };
      goose = pkgs.buildGoModule {
        name = "goose";
        src = pkgs.fetchFromGitHub {
          owner = "goose-lang";
          repo = "goose";
          rev = "67cf95ebfc80e80ddc40b0518e6d761cde44977c";
          sha256 = "16040c4frxn9dk3xmajzg4jb7fi7q39hasfp94rpnphmpr4hvr51";
        };
        vendorHash = "sha256-HCJ8v3TSv4UrkOsRuENWVz5Z7zQ1UsOygx0Mo7MELzY=";
      };
      vscode-marketplace = inputs.nix-vscode-extensions.extensions.${system}.vscode-marketplace;
      vscode = import /research/nix/vscode-no-state.nix {
        inherit pkgs vscode-marketplace;

        settings = codium_settings;
        vscodeExtensions = with vscode-marketplace; [
          maximedenes.vscoq
          leanprover.lean4
        ];
      };
      
    in
      pkgs.mkShell {
        packages = [
          # coq deps
          pkgs.coq
          pkgs.rocqPackages.stdlib
          pkgs.coqPackages.vscoq-language-server

          vscode

          pkgs.python3

          pkgs.go
          grackle
          goose
          pkgs.protobuf

          # nix helper
          # Should be able to update goose and grackle with `update-nix-fetchgit flake.nix`
          pkgs.update-nix-fetchgit
          pkgs.nix-prefetch-git
          pkgs.nix-prefetch
        ];

            shellHook = ''
              unset COQPATH
            '';
          };
      };
}
