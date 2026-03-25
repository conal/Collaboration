{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    felix = {
      url = "github:conal/felix";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" ];
      perSystem = { self', system, pkgs, ... }: {
        devShells.default =
          let
            agdaWithStdlib = pkgs.agda.withPackages (p: [ p.standard-library ]);
            felixCompiled = pkgs.stdenv.mkDerivation {
              name = "felix-compiled";
              src = inputs.felix;
              nativeBuildInputs = [ agdaWithStdlib ];
              buildPhase = ''
                mkdir -p $out/src
                cp -r src/. $out/src/
                cd $out
                agda -i src -i ${pkgs.agdaPackages.standard-library}/src src/Felix/Homomorphism.agda
              '';
              installPhase = ":";
            };
            myAgda = pkgs.symlinkJoin {
              name = "agda-with-felix";
              paths = [ agdaWithStdlib ];
              buildInputs = [ pkgs.makeWrapper ];
              postBuild = ''
                wrapProgram $out/bin/agda \
                  --add-flags "-i ${felixCompiled}/src"
              '';
            };
          in
          pkgs.mkShell {
            nativeBuildInputs = [
              myAgda
              pkgs.glibcLocales
            ];
            shellHook = ''
              export LOCALE_ARCHIVE="${pkgs.glibcLocales}/lib/locale/locale-archive"
              export LC_ALL="en_US.UTF-8"
              echo "Agda ready. Compile with:"
              echo "  agda --compile limited-recursion/telomare.agda"
            '';
          };

        packages.default =
          let
            stdlib = pkgs.agdaPackages.standard-library;
          in
          pkgs.stdenv.mkDerivation {
            name = "agda-telomare";
            src = pkgs.lib.cleanSource ./limited-recursion;
            nativeBuildInputs = [ pkgs.agda pkgs.ghc pkgs.glibcLocales ];
            LOCALE_ARCHIVE = "${pkgs.glibcLocales}/lib/locale/locale-archive";
            LC_ALL = "en_US.UTF-8";
            buildPhase = ''
              cp -r ${inputs.felix}/src felix-src
              chmod -R u+w felix-src
              agda -i ${stdlib}/src -i felix-src --compile telomare.agda
            '';
            installPhase = ''
              mkdir -p $out/bin
              cp telomare $out/bin/agda-telomare
            '';
          };

        apps.default = {
          type = "app";
          program = "${self'.packages.default}/bin/agda-telomare";
        };

        checks.fib = pkgs.runCommand "check-fib" {
          LOCALE_ARCHIVE = "${pkgs.glibcLocales}/lib/locale/locale-archive";
          LC_ALL = "en_US.UTF-8";
        } ''
          actual=$(${self'.packages.default}/bin/agda-telomare)
          expected=$(cat <<'EXPECTED'
── Object-language fibonacci (§11): syntax → ⟦_⟧ → run ──
fibS( 0) = 0  [tel remaining: 1]
fibS( 1) = 1  [tel remaining: 1]
fibS( 5) = 5  [tel remaining: 1]
fibS(10) = 55  [tel remaining: 1]
Out-of-tel: fibS(10) with tel 5 → ?

── Semantic-domain fibonacci (§12): direct Kleisli ──
fib( 0) = 0  [tel remaining: 1]
fib( 1) = 1  [tel remaining: 1]
fib( 2) = 1  [tel remaining: 1]
fib( 3) = 2  [tel remaining: 1]
fib( 4) = 3  [tel remaining: 1]
fib( 5) = 5  [tel remaining: 1]
fib( 6) = 8  [tel remaining: 1]
fib( 7) = 13  [tel remaining: 1]
fib( 8) = 21  [tel remaining: 1]
fib( 9) = 34  [tel remaining: 1]
fib(10) = 55  [tel remaining: 1]

Out-of-tel: fib(10) with tel 5 → ?
EXPECTED
          )
          if [ "$actual" = "$expected" ]; then
            echo "PASS: fibonacci output matches expected"
            mkdir -p $out
            echo "$actual" > $out/result.txt
          else
            echo "FAIL: output mismatch"
            echo "=== Expected ==="
            echo "$expected"
            echo "=== Actual ==="
            echo "$actual"
            diff <(echo "$expected") <(echo "$actual") || true
            exit 1
          fi
        '';
      };
    };
}
