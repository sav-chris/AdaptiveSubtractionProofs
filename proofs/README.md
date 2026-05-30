# adaptive_subtraction

### Install Dependencies

Install Chocolatey if you need it
```powershell
iwr https://community.chocolatey.org/install.ps1 -UseBasicParsing | iex
```

Install L∃∀N
```powershell
choco install lean
```

Install WSL
```powershell
wsl --install
```

Install Docker 
```powershell
winget install -e --id Docker.DockerDesktop
```

Restart Terminal, install lean dependencies

```powershell
lake update
```

# Clone Repo
```powershell
git clone https://github.com/sav-chris/AdaptiveSubtractionProofs.git

cd AdaptiveSubtractionProofs/proofs
```

# Running in Docker

Start Docker desktop

Start the container
```powershell
docker compose up
```

# Running Locally 

```powershell
lake update
```

```powershell
lake build
```
