unit BlackHole;

{$mode objfpc}{$H+}
{$i blackhole.inc}

interface

uses
  Classes, SysUtils, FileUtil, StrUtils, SynCommons, SynZip, SynCrypto, mORMot,
  MTProcs, Crypto, Network, BlockStack, Gaia;

type
  TBHKey = RawUTF8;
  TBHDeviceID = RawUTF8;
  TBHManagerStatus = (bhmsNone, bhmsConnectionProblem, bhmsNeedAuthentication,
    bhmsReady, bhmsStartingUpload,
    bhmsUploading, bhmsUploadError);
  TBHShareState = (bssPending, bssInitializing, bssChecking, bssChecked,
    bssPreparing, bssRunning, bssPaused, bssStoped, bssFinished);
  TBHErrorKind = (bekNone, bekUnknown, bekEncryptError, bekExceedSizeLimit,
    bekFileNotFound, bekRequestEntityTooLarge,
    bekInvalidFile, bekSSLError, bekEmptyFile, bekInvalidName,
    bekInvalidProvider, bekUnavailableProvider,
    bekNeedAuthentication, bekFailedAuthentication, bekTemporarilyUnavailable,
    bekInvalidInputPrivateKey, bekInvalidResponse, bekMultiPublicKeys,
    bekInvalidSignature,
    bekInvalidAddress, bekInvalidUserName, bekInvalidPrivateKey,
    bekNoConnection, bekCanNotMakeStorageFile, bekUnavailableShortenerProvider);
  TBHErrorKinds = set of TBHErrorKind;
  TBHManagerOption = (bmoLocalStorage, bmoTestHub, bmoNoEncryption,
    bmoNoFileCompression);
  TBHManagerOptions = set of TBHManagerOption;
  TBHManager = class;
  TBHProvider = class;
  TBHLinkShortener = class;

  { BHException }

  BHException = class(Exception)
  private
    FError: TBHErrorKind;
  public
    constructor Create(AError: TBHErrorKind); overload;
    property Error: TBHErrorKind read FError;
  end;

  { TBHFile }

  TBHFile = class(TSQLRecord)
  private
    FName: TFileName;
    FParts: TRawUTF8DynArray;
    FPartSize: int64;
    FRecipe: TRawUTF8DynArray;
    FSize: int64;
    function GetFinishedPartCount: integer;
    function GetPartCount: integer;
  public
    function ToJSON: RawJSON;
    function FromJSON(const AValue: RawJSON): boolean;
    property PartCount: integer read GetPartCount;
    property FinishedPartCount: integer read GetFinishedPartCount;
  published
    property Name: TFileName read FName write FName;
    property Size: int64 read FSize write FSize;
    property Recipe: TRawUTF8DynArray read FRecipe write FRecipe;
    property PartSize: int64 read FPartSize write FPartSize;
    property Parts: TRawUTF8DynArray read FParts write FParts;
  end;

  { TBHShare }

  TBHShare = class(TSQLRecord)
  private
    FError: TBHErrorKind;
    FFileName: TFileName;
    FKey: TBHKey;
    FPassword: RawUTF8;
    FShortURL: RawUTF8;
    FState: TBHShareState;
    FURL: RawUTF8;
    function GetURL: RawUTF8;
    procedure SetError(AValue: TBHErrorKind);
    procedure SetFileName(AValue: TFileName);
    procedure SetKey(AValue: TBHKey);
    procedure SetPassword(AValue: RawUTF8);
  public
    property URL: RawUTF8 read GetURL;
    property ShortURL: RawUTF8 read FShortURL;
  published
    property FileName: TFileName read FFileName write SetFileName;
    property Key: TBHKey read FKey write SetKey;
    property Password: RawUTF8 read FPassword write SetPassword;
    property State: TBHShareState read FState write FState;
    property Error: TBHErrorKind read FError write SetError;
  end;

  { TBHShareRequest }

  TBHShareRequest = class(TSynAutoCreateFields)
  private
    FEnableShortLinkGeneration: boolean;
    FFinishTime: TDateTime;
    function CancelPart: boolean;
    function GetProgress: single;
    function GetUploadProgress: single;
  protected
    Manager: TBHManager;
    FFileName, FShareFileName, TempFileName: TFileName;
    Provider: TBHProvider;
    Stream: TStream;
    Size: int64;
    FShare: TBHShare;
    FFile: TBHFile;
    Safe, FileSyncSafe: TSynLocker;
    FPrepareProgress: single;
    FPrepareWeight: single;
    LastFileSyncTime: QWord;
    Terminated: boolean;
    ShortPK: IECPrivateKeyParameters;
    ShortPass: RawUTF8;
    procedure SyncUpdateStatus;
    procedure UpdateStatus;
    function Check(AError: TBHErrorKind): boolean; overload;
    function Check: boolean; overload;
    procedure SetState(AValue: TBHShareState);
    procedure SetError(AValue: TBHErrorKind);
    function UploadFile: TBHErrorKind;
    function UploadHistory: TBHErrorKind;
    procedure UploadPart(AIndex: PtrInt; AData: Pointer; AItem: TMultiThreadProcItem);
    function GenerateShortLink: TBHErrorKind;
    function IsCompressible(const AFileName: TFileName): boolean;
  protected
    function CheckSize: TBHErrorKind; virtual;
    function Prepare: TBHErrorKind; virtual;
    procedure InternalRun; virtual;
  public
    constructor Create(AManager: TBHManager; AFileName: TFileName); virtual; overload;
    destructor Destroy; override;
    procedure Run;
    property UploadProgress: single read GetUploadProgress;
    property Progress: single read GetProgress;
  published
    property FileName: TFileName read FFileName;
    property ShareFileName: TFileName read FShareFileName;
    property Share: TBHShare read FShare;
    property File_: TBHFile read FFile;
    property PrepareProgress: single read FPrepareProgress;
    property PrepareWeight: single read FPrepareWeight;
    property FinishTime: TDateTime read FFinishTime;
    property EnableShortLinkGeneration: boolean read FEnableShortLinkGeneration write FEnableShortLinkGeneration;
  end;

  TBHCancelFunction = function: boolean of object;

  { TBHProvider }

  TBHProvider = class
  protected
    function DoSetData(const AKey: RawUTF8; const AValue: RawByteString): TBHErrorKind; virtual; abstract;
    function DoGetData(const AKey: RawUTF8; out AValue: RawByteString): TBHErrorKind; virtual; abstract;
  public
    function SetData(const AKey: RawUTF8; const AValue: RawByteString; ATryLimit: integer; ACancel: TBHCancelFunction = nil): TBHErrorKind;
    function GetData(const AKey: RawUTF8; out AValue: RawByteString; ATryLimit: integer; ACancel: TBHCancelFunction = nil): TBHErrorKind;
    function GetFullName(const AKey: RawUTF8): RawUTF8; virtual; abstract;
  end;

  { TBHLocalProvider }

  TBHLocalProvider = class(TBHProvider)
  private
    FDirectory: TFileName;
  protected
    function DoSetData(const AKey: RawUTF8; const AValue: RawByteString): TBHErrorKind; override;
    function DoGetData(const AKey: RawUTF8; out AValue: RawByteString): TBHErrorKind; override;
  public
    constructor Create(ADirectory: TFileName);
    function GetFullName(const AKey: RawUTF8): RawUTF8; override;
  published
    property Directory: TFileName read FDirectory write FDirectory;
  end;

  { TBHGaiaProvider }

  TBHGaiaProvider = class(TBHProvider)
  private
    FHub: TGaiaHub;
    FOwned: boolean;
    function NetworkErrorToBHError(AValue: TNetworkErrorKind): TBHErrorKind;
  protected
    function DoSetData(const AKey: RawUTF8; const AValue: RawByteString): TBHErrorKind; override;
    function DoGetData(const AKey: RawUTF8; out AValue: RawByteString): TBHErrorKind; override;
  public
    constructor Create(AHub: TGaiaHub; AOwned: boolean);
    destructor Destroy; override;
    function GetFullName(const AKey: RawUTF8): RawUTF8; override;
  published
    property Hub: TGaiaHub read FHub;
  end;

  TBHManagerShareNotifyEvent = procedure(Sender: TBHManager; ARequest: TBHShareRequest) of object;
  TBHManagerSignInRequestEvent = procedure(Sender: TBHManager; ARequest: RawUTF8) of object;
  TBHManagerHandleSignInResponseEvent = procedure(Sender: TBHManager; AError: TBHErrorKind) of object;

  { TBHManager }

  TBHManager = class
  private
    FDeviceID: TBHDeviceID;
    FLinkShortener: TBHLinkShortener;
    FOnSignInRequest: TBHManagerSignInRequestEvent;
    FOnStatusChange: TNotifyEvent;
    FOptions: TBHManagerOptions;
    FPrepared: boolean;
    FProvider: TBHProvider;
    FOnUploadChange: TBHManagerShareNotifyEvent;
    FAuth: TBlockStack;
    FStatus: TBHManagerStatus;
    FCurrentRequest: TBHShareRequest;
    SignInPrivateKey: IECPrivateKeyParameters;
    function GetInfoStorageName: TFileName;
    function GetIsStorageValid: boolean;
    procedure SetOptions(AValue: TBHManagerOptions);
    procedure SetStatus(AValue: TBHManagerStatus);
  protected
    function Init: TBHErrorKind;
    function LoadInfo(AJustCheck: boolean): boolean;
    function SaveInfo: boolean;
    function ClearInfo: boolean;
    function MakeProvider(ARandom: boolean): TBHProvider;
    function MakeGaiaProvider(AHost: RawUTF8; APrivateKey: IECPrivateKeyParameters): TBHGaiaProvider;
    procedure DoUpload(ARequest: TBHShareRequest);
    procedure UpdateUpload(ARequest: TBHShareRequest);
    function BlockStackErrorToBHError(AValue: TBlockStackErrorKind): TBHErrorKind;
    function Encrypt(const AKey: RawUTF8; const AInput: RawByteString; ALength: integer; out AOutput: RawByteString): boolean; overload;
    function Encrypt(const AKey: RawUTF8; const AInput: RawByteString; out AOutput: RawByteString): boolean; overload;
    function Decrypt(const AKey: RawUTF8; const AInput: RawByteString; out AOutput: RawByteString): boolean; overload;
    function Encrypt(const AInput: RawByteString; out AOutput: RawByteString): boolean; overload;
    function Decrypt(const AInput: RawByteString; out AOutput: RawByteString): boolean; overload;
  public
    constructor Create(AOptions: TBHManagerOptions);
    destructor Destroy; override;
    function Prepare: TBHErrorKind;
    function Clear: boolean;
    function HandleSignInResponse(const AResponse: RawUTF8): TBHErrorKind;
    function Add(ARequest: TBHShareRequest): integer;
    function Stop(ARequest: TBHShareRequest): boolean;
    function GetShareFullURL(AShare: TBHShare): RawUTF8;
  published
    property Options: TBHManagerOptions read FOptions;
    property Status: TBHManagerStatus read FStatus;
    property Auth: TBlockStack read FAuth;
    property Prepared: boolean read FPrepared;
    property Provider: TBHProvider read FProvider;
    property LinkShortener: TBHLinkShortener read FLinkShortener;
    property DeviceID: TBHDeviceID read FDeviceID;
    property InfoStorageName: TFileName read GetInfoStorageName;
    property IsStorageValid: boolean read GetIsStorageValid;
    property OnStatusChange: TNotifyEvent read FOnStatusChange write FOnStatusChange;
    property OnSignInRequest: TBHManagerSignInRequestEvent read FOnSignInRequest write FOnSignInRequest;
    property OnUploadChange: TBHManagerShareNotifyEvent read FOnUploadChange write FOnUploadChange;
  end;

  { TBHManagerInfoStorage }

  TBHManagerInfoStorage = class
  private
    FDeviceID: RawUTF8;
    FPrivateKey: RawUTF8;
    FVersion: integer;
  published
    property Version: integer read FVersion write FVersion;
    property PrivateKey: RawUTF8 read FPrivateKey write FPrivateKey;
    property DeviceID: RawUTF8 read FDeviceID write FDeviceID;
  end;

  { TBHLinkShortener }

  TBHLinkShortener = class
  private
    FProvider: TBHProvider;
    FManager: TBHManager;
    function GetPrivateKey: IECPrivateKeyParameters;
  public
    constructor Create(AManager: TBHManager);
    destructor Destroy; override;
    function Prepare: TBHErrorKind;
    function GenerateLink(AURL: RawByteString; APrivateKey: IECPrivateKeyParameters; APass: RawUTF8): string;
  public
  end;

const
  BH_VERSION = 5;
  BH_DEFAULT_TRY_COUNT = 180;
  BH_CONNECTION_COUNT = 4;
  BH_DATA_SIZE_LIMIT = 0.5 * 1024 * 1024 * 1024;
  BH_DATA_COMPRESSE_COUNT_LIMIT = 1000;
  BH_HOST = 'blackhole.run';
  BH_DOMAIN = 'https://blackhole.run';
  BH_SIGNIN_REDIRECT_URL = 'https://blackhole.run/redirect';
  BH_MANIFEST_URL = 'https://blackhole.run/manifest.json';
  BH_SHARE_URL = 'https://app.blackhole.run/#';
  BH_LINK_SHORTENER_GAIA_HUB_URL = 'https://hub.blockstack.org';

var
  BHTestGaiaURL: string;
  BHTestShareURL: string;

implementation

uses  Math;

{ TBHLinkShortener }

function TBHLinkShortener.GetPrivateKey: IECPrivateKeyParameters;
begin
  Result := TBHGaiaProvider(FProvider).Hub.PrivateKey;
end;

constructor TBHLinkShortener.Create(AManager: TBHManager);
begin
  FManager := AManager;
end;

destructor TBHLinkShortener.Destroy;
begin
  if (FProvider <> nil) then
    FProvider.Free;
  inherited Destroy;
end;

function TBHLinkShortener.Prepare: TBHErrorKind;
begin
  Result := bekNone;
  FProvider := FManager.MakeGaiaProvider(BH_LINK_SHORTENER_GAIA_HUB_URL, TCrypto.GeneratePrivateKey);
  if FProvider is TBHGaiaProvider then
    if not TBHGaiaProvider(FProvider).Hub.Prepare then
    begin
      Result := bekUnavailableShortenerProvider;
      FreeAndNil(FProvider);
    end;
end;

function TBHLinkShortener.GenerateLink(AURL: RawByteString; APrivateKey: IECPrivateKeyParameters; APass: RawUTF8): string;
var
  EncBuf: RawByteString;
begin
  Result := '';
  with TBHGaiaProvider(FProvider).Hub do
  begin
    PrivateKey := APrivateKey;
    if (Prepare) then
    begin
      EncBuf := TCrypto.EncryptPKCS7(APass, Address, 60000, AURL, True);
      if (FProvider.SetData('url', EncBuf, BH_DEFAULT_TRY_COUNT) = bekNone) then
        Result := APass + Address;
    end;
  end;
end;

{ TBHGaiaProvider }

function TBHGaiaProvider.NetworkErrorToBHError(AValue: TNetworkErrorKind): TBHErrorKind;
const
  Er: array[TNetworkErrorKind] of TBHErrorKind = (bekNone, bekUnknown, bekFileNotFound,
    bekRequestEntityTooLarge, bekTemporarilyUnavailable, bekFailedAuthentication, bekTemporarilyUnavailable);
begin
  Result := Er[AValue];
end;

function TBHGaiaProvider.DoSetData(const AKey: RawUTF8; const AValue: RawByteString): TBHErrorKind;
var
  PubURL: RawUTF8;
begin
  Result := NetworkErrorToBHError(Hub.Upload(AKey, AValue, PubURL));
end;

function TBHGaiaProvider.DoGetData(const AKey: RawUTF8; out AValue: RawByteString): TBHErrorKind;
begin
  Result := NetworkErrorToBHError(Hub.Download(AKey, AValue));
end;

constructor TBHGaiaProvider.Create(AHub: TGaiaHub; AOwned: boolean);
begin
  FHub := AHub;
  FOwned := AOwned;
end;

destructor TBHGaiaProvider.Destroy;
begin
  inherited Destroy;
  if FOwned then
    FHub.Free;
end;

function TBHGaiaProvider.GetFullName(const AKey: RawUTF8): RawUTF8;
begin
  Result := Hub.GetFileURL(AKey, False);
end;

{ TBHProvider }

function TBHProvider.SetData(const AKey: RawUTF8; const AValue: RawByteString; ATryLimit: integer; ACancel: TBHCancelFunction): TBHErrorKind;
var
  TryCount: integer;
begin
  TryCount := 0;
  repeat
    Result := DoSetData(AKey, AValue);
    if Assigned(ACancel) and ACancel() then
      Exit;
    TryCount += 1;
    case Result of
      bekInvalidName: Break;
      bekTemporarilyUnavailable: Sleep(1000);
      bekFailedAuthentication: Exit;
    end;
  until (Result = bekNone) or (TryCount = ATryLimit);
end;

function TBHProvider.GetData(const AKey: RawUTF8; out AValue: RawByteString; ATryLimit: integer; ACancel: TBHCancelFunction): TBHErrorKind;
var
  TryCount: integer;
begin
  TryCount := 0;
  repeat
    Result := DoGetData(AKey, AValue);
    if Assigned(ACancel) and ACancel() then
      Exit;
    TryCount += 1;
    case Result of
      bekFileNotFound: Break;
      bekInvalidName: Break;
      bekTemporarilyUnavailable: Sleep(1000);
      bekFailedAuthentication: Exit;
    end;
  until (Result = bekNone) or (TryCount = ATryLimit);
end;

{ BHException }

constructor BHException.Create(AError: TBHErrorKind);
begin
  inherited Create(GetCaptionFromEnum(TypeInfo(TBHErrorKind), integer(AError)));
  FError := AError;
end;

{ TBHShareRequest }

function TBHShareRequest.CancelPart: boolean;
begin
  Result := Check;
end;

function TBHShareRequest.GetProgress: single;
begin
  Result := (PrepareProgress * PrepareWeight) + (UploadProgress * (1 - PrepareWeight));
end;

function TBHShareRequest.GetUploadProgress: single;
begin
  with File_ do
    Result := FinishedPartCount / Max(PartCount, 1);
end;

procedure TBHShareRequest.SyncUpdateStatus;
begin
  Manager.UpdateUpload(Self);
end;

procedure TBHShareRequest.UpdateStatus;
begin
  if Terminated then
    Exit;
  if Share.State in [bssStoped, bssFinished] then
    FFinishTime := Now;
  TThread.Synchronize(TThread.CurrentThread, @SyncUpdateStatus);
end;

function TBHShareRequest.Check(AError: TBHErrorKind): boolean;
begin
  if Terminated then
    Exit(True);
  Share.Error := AError;
  Result := Self.Check;
  if Result then
    UpdateStatus;
end;

function TBHShareRequest.Check: boolean;
begin
  if Terminated then
    Exit(True);
  Result := Share.State = bssStoped;
end;

procedure TBHShareRequest.SetState(AValue: TBHShareState);
begin
  if Terminated then
    Exit;
  if Share.State = AValue then
    Exit;
  Share.State := AValue;
  UpdateStatus;
end;

procedure TBHShareRequest.SetError(AValue: TBHErrorKind);
begin
  if Terminated then
    Exit;
  if Share.Error = AValue then
    Exit;
  Share.Error := AValue;
end;

function TBHShareRequest.UploadFile: TBHErrorKind;
var
  Buf, EncBuf: RawByteString;
begin
  Buf := FFile.ToJSON;
  if not (bmoNoFileCompression in Manager.Options) then
    CompressDeflate(Buf, True);
  if Manager.Encrypt(Share.Key, Buf, EncBuf) then
    Result := Provider.SetData(ExtractFileName(Share.FileName), EncBuf, BH_DEFAULT_TRY_COUNT)
  else
    Result := bekEncryptError;
end;

function TBHShareRequest.UploadHistory: TBHErrorKind;
var
  Buf, EncBuf: RawByteString;
  FN: string;
  PK, SHPK: RawUTF8;
begin
  if Provider is TBHGaiaProvider then
    PK := TCrypto.PrivateKeyAsString(TBHGaiaProvider(Provider).Hub.PrivateKey)
  else
    PK := '';
  if (ShortPK <> nil) then
    SHPK := TCrypto.PrivateKeyAsString(ShortPK)
  else
    SHPK := '';
  with Share do
    Buf := JSONEncode(['BHV', BH_VERSION, 'PK', PK, 'FN', FileName, 'KY', Key, 'SHPK', SHPK, 'SHPA', ShortPass]);
  FN := Manager.DeviceID + '_' + IntToString(UnixTimeUTC);
  if Manager.Encrypt(Buf, EncBuf) then
    Result := Manager.Provider.SetData(FN, EncBuf, BH_DEFAULT_TRY_COUNT)
  else
    Result := bekEncryptError;
end;

procedure TBHShareRequest.UploadPart(AIndex: PtrInt; AData: Pointer; AItem: TMultiThreadProcItem);
var
  Buf, EncBuf: RawByteString;
  R: int64;
  PH: RawUTF8;
  E: TBHErrorKind;
begin
  if Check then
    Exit;
  Buf := '';
  SetLength(Buf, FFile.PartSize);
  Safe.Lock;
  try
    Stream.Position := AIndex * FFile.PartSize;
    R := Stream.Read(Buf[1], FFile.PartSize);
  finally
    Safe.UnLock;
  end;
  if not Manager.Encrypt(Share.Key, Buf, R, EncBuf) then
    raise BHException.Create(bekEncryptError);
  PH := HashFull(hfSHA256, @EncBuf[1], Length(EncBuf));
  if Check then
    Exit;
  E := Provider.SetData(PH, EncBuf, BH_DEFAULT_TRY_COUNT, @CancelPart);
  if E <> bekNone then
    raise BHException.Create(E);
  if Check then
    Exit;
  FFile.FParts[AIndex] := PH;
  if Check then
    Exit;
  Safe.Lock;
  try
    UpdateStatus;
  finally
    Safe.UnLock;
  end;
  if Check then
    Exit;
  if FileSyncSafe.TryLock then
    try
      if (SysUtils.GetTickCount64 - LastFileSyncTime > 1000) then
      begin
        LastFileSyncTime := SysUtils.GetTickCount64;
        UploadFile;
      end;
    finally
      FileSyncSafe.UnLock;
    end;
end;

function TBHShareRequest.GenerateShortLink: TBHErrorKind;
begin
  Result := bekNone;
  ShortPK := TCrypto.GeneratePrivateKey;
  ShortPass := TCrypto.RandomURLSafePassword(10);
  Share.FShortURL := Manager.LinkShortener.GenerateLink(Share.URL, ShortPK, ShortPass);
end;

function TBHShareRequest.IsCompressible(const AFileName: TFileName): boolean;
const
  TestSize = 10 * 1024;
  Ext: array of string = (
    'bmp', 'tif', 'tiff',
    'avi',
    'txt', 'json', 'xml');
  CompExt: array of string = (
    'jpg', 'png', 'gif',
    'mp3', 'flac', 'wma', 'ogg',
    'mp4', 'mov', 'wmv', 'webp', 'mkv',
    'zip', 'rar', 'gz', 'tar', 'cab');
var
  Str: TFileStream;
  Buf: RawUTF8;
  E: string;
begin
  E := ExtractFileExt(AFileName);
  E := LowerCase(E);
  if Length(E) > 1 then
  begin
    Delete(E, 1, 1);
    if E in Ext then
      Exit(True);
    if E in CompExt then
      Exit(False);
  end;
  try
    Str := TFileStream.Create(AFileName, fmOpenRead or fmShareDenyNone);
    Buf := ReadStringFromStream(Str, 16);
    SetLength(Buf, 16);
    Str.Read(Buf[1], Length(Buf));
    Result := not SynCommons.IsContentCompressed(Pointer(Buf), Length(Buf));
    if Result then
      Exit;
    if Str.Size <= TestSize * 2 then
      Exit;
    Str.Position := (Str.Size - TestSize) div 2;
    SetLength(Buf, TestSize);
    Str.Read(Buf[1], Length(Buf));
    CompressZLib(Buf, True);
    Result := Length(Buf) / TestSize > 0.1;
  finally
    Str.Free;
  end;
end;

function TBHShareRequest.CheckSize: TBHErrorKind;
begin
  Result := bekNone;
  if not FileExists(FileName) then
    Exit(bekFileNotFound);
  Size := FileUtil.FileSize(FileName);
  if Size > BH_DATA_SIZE_LIMIT then
    Exit(bekExceedSizeLimit);
  if Size <= 0 then
    Exit(bekEmptyFile);
end;

function TBHShareRequest.Prepare: TBHErrorKind;
var
  Compressible: boolean;
  Str: TFileStream;
  ChunkSize, ChunkCount: int64;
  i: integer;
begin
  Result := bekNone;
  Compressible := (Size > 150) and IsCompressible(FileName);
  FPrepareWeight := IfThen(Compressible, 0.1, 0.01);
  try
    Str := TFileStream.Create(FileName, fmOpenRead or fmShareDenyNone);
  except
    Exit(bekInvalidFile);
  end;

  if Compressible then
  begin
    ChunkSize := Max(Str.Size div 100, 2 * 1024 * 1024);
    ChunkCount := Str.Size div ChunkSize;
    if ChunkCount * ChunkSize < Str.Size then
      ChunkCount += 1;

    TempFileName := TemporaryFileName;
    Stream := TFileStream.Create(TempFileName, fmCreate);
    with TSynZipCompressor.Create(Stream, 6, szcfRaw) do
      try
        for i := 0 to ChunkCount - 1 do
        begin
          CopyFrom(Str, Min(ChunkSize, Str.Size - Str.Position));
          FPrepareProgress := (i + 1) / ChunkCount;
          UpdateStatus;
          if Check then
            Exit;
        end;
      finally
        Free;
      end;

    if Stream.Size < Size then
    begin
      Str.Free;
      FFile.Recipe := ['deflateRaw'];
    end
    else
    begin
      Stream.Free;
      Stream := Str;
    end;
  end
  else
  begin
    Stream := Str;
    FPrepareProgress := 1;
    UpdateStatus;
  end;
end;

procedure TBHShareRequest.InternalRun;
var
  PartCount: int64;
begin
  SetState(bssInitializing);
  if Provider is TBHGaiaProvider then
    if not TBHGaiaProvider(Provider).Hub.Prepare then
    begin
      Check(bekInvalidProvider);
      Exit;
    end;
  SetState(bssChecking);
  if Check(CheckSize) then
    Exit;
  Share.FileName := Provider.GetFullName(LowerCase(TAESPRNG.Main.FillRandomHex(3)));
  Share.Key := LowerCase(TAESPRNG.Main.FillRandomHex(32));
  SetState(bssChecked);
  SetState(bssPreparing);
  if Check(Prepare) then
    Exit;
  FFile.Size := Size;
  FFile.Name := ShareFileName;
  if Stream.Size <= 25 * 1024 * 1024 then
    FFile.PartSize := 512 * 1024
  else
    FFile.PartSize := Min(2 * 1024 * 1024, Stream.Size div 50);
  PartCount := Stream.Size div FFile.PartSize;
  if PartCount * FFile.PartSize < Stream.Size then
    PartCount += 1;
  SetLength(FFile.FParts, PartCount);
  if Check(UploadFile) then
    Exit;
  if (FEnableShortLinkGeneration) then
    if (Check(GenerateShortLink)) then
      Exit;
  SetState(bssRunning);
  try
    UploadPart(0, nil, nil);
    if Check then
      Exit;
    with TProcThreadPool.Create do
      try
        MaxThreadCount := BH_CONNECTION_COUNT;
        DoParallel(@UploadPart, 1, PartCount - 1);
      finally
        Free;
      end;
  except
    on E: BHException do
    begin
      Check(E.Error);
      Exit;
    end;
  end;
  if Check then
    Exit
  else
  if FFile.FinishedPartCount <> FFile.PartCount then
    Check(bekUnknown)
  else if (not Check(UploadFile)) and (not Check(UploadHistory)) then
    SetState(bssFinished);
end;

procedure TBHShareRequest.Run;
begin
  Provider := Manager.MakeProvider(True);
  TBHGaiaProvider(Provider).Hub.SetHubInfo(TBHGaiaProvider(Manager.Provider).Hub.UrlPerfix, TBHGaiaProvider(Manager.Provider).Hub.ChallengeText);
  Safe.Init;
  FileSyncSafe.Init;
  try
    InternalRun;
  finally
    Provider.Free;
    Stream.Free;
    DeleteFile(TempFileName);
    FileSyncSafe.Done;
    Safe.Done;
  end;
end;

constructor TBHShareRequest.Create(AManager: TBHManager; AFileName: TFileName);
begin
  inherited Create;
  Terminated := False;
  Manager := AManager;
  FFileName := AFileName;
  FShareFileName := ExtractFileName(FFileName);
end;

destructor TBHShareRequest.Destroy;
begin
  Terminated := True;
  inherited Destroy;
  Self := nil;
end;

{ TBHLocalProvider }

function TBHLocalProvider.DoSetData(const AKey: RawUTF8; const AValue: RawByteString): TBHErrorKind;
begin
  Sleep(200);
  try
    if FileFromString(AValue, GetFullName(AKey)) then
      Result := bekNone
    else
      Result := bekInvalidName;
  except
    Result := bekUnknown;
  end;
end;

function TBHLocalProvider.DoGetData(const AKey: RawUTF8; out AValue: RawByteString): TBHErrorKind;
var
  FN: TFileName;
begin
  FN := GetFullName(AKey);
  try
    if FileExists(FN) then
    begin
      AValue := StringFromFile(FN);
      Result := bekNone;
    end
    else
      Result := bekFileNotFound;
  except
    Result := bekUnknown;
  end;
end;

constructor TBHLocalProvider.Create(ADirectory: TFileName);
begin
  EnsureDirectoryExists(GetFullName(''), True);
  FDirectory := ADirectory;
  EnsureDirectoryExists(GetFullName(''), True);
end;

function TBHLocalProvider.GetFullName(const AKey: RawUTF8): RawUTF8;
begin
  Result := ExtractFilePath(ParamStr(0)) + 'Storage' + PathDelim;
  if FDirectory <> '' then
    Result += FDirectory + PathDelim;
  Result += AKey;
end;

{ TBHShare }

function TBHShare.GetURL: RawUTF8;
var
  Salt: RawUTF8;
  EncResult: RawByteString;
begin
  if Error <> bekNone then
    Exit('');
  if FURL <> '' then
    Exit(FURL);
  Result := JSONEncode(['BHV', BH_VERSION, 'FN', FileName, 'KY', Key]);
  if Password <> '' then
  begin
    Salt := TAESPRNG.Main.FillRandomHex(16);
    EncResult := TCrypto.EncryptPKCS7(Password, Salt, 60000, Result, True);
    Result := JSONEncode(['BHV', BH_VERSION, 'SL', Salt, 'CN', BinToBase64uri(EncResult)]);
  end;
  CompressDeflate(Result, True);
  Result := BinToBase64uri(Result);
  FURL := Result;
end;

procedure TBHShare.SetError(AValue: TBHErrorKind);
begin
  if AValue = FError then
    Exit;
  FError := AValue;
  FState := bssStoped;
end;

procedure TBHShare.SetFileName(AValue: TFileName);
begin
  if FFileName = AValue then
    Exit;
  FFileName := AValue;
  FURL := '';
end;

procedure TBHShare.SetKey(AValue: TBHKey);
begin
  if FKey = AValue then
    Exit;
  FKey := AValue;
  FURL := '';
end;

procedure TBHShare.SetPassword(AValue: RawUTF8);
begin
  if FPassword = AValue then
    Exit;
  FPassword := AValue;
  FURL := '';
end;

{ TBHFile }

function TBHFile.GetFinishedPartCount: integer;
var
  P: RawUTF8;
begin
  Result := 0;
  for P in FParts do
    if P <> '' then
      Result += 1;
end;

function TBHFile.GetPartCount: integer;
begin
  Result := Length(FParts);
end;

function TBHFile.ToJSON: RawJSON;
begin
  Result := '';
  with TTextWriter.CreateOwnedStream do
    try
      Add('{');
      AddFieldName('Name');
      AddJSONString(Name);
      Add(',');
      AddFieldName('Size');
      Add(Size);
      Add(',');
      if Length(Recipe) <> 0 then
      begin
        AddFieldName('Recipe');
        AddDynArrayJSON(TypeInfo(TRawUTF8DynArray), FRecipe);
        Add(',');
      end;
      AddFieldName('PartSize');
      Add(PartSize);
      Add(',');
      AddFieldName('Parts');
      AddDynArrayJSON(TypeInfo(TRawUTF8DynArray), FParts);
      Add('}');
      SetText(Result);
    finally
      Free
    end;
end;

function TBHFile.FromJSON(const AValue: RawJSON): boolean;
var
  Vs: array[0..4] of TValuePUTF8Char;
begin
  Result := JSONDecode(Pointer(AValue), ['Name', 'Mime', 'Recipe', 'PartSize', 'Parts'],
    @Vs, True) <> nil;
  if not Result then
    Exit;
  Name := Vs[0].ToString;
  Size := Vs[1].ToInteger;
  DynArrayLoadJSON(FRecipe, Vs[2].Value, TypeInfo(TRawUTF8DynArray));
  PartSize := Vs[3].ToInteger;
  DynArrayLoadJSON(FParts, Vs[4].Value, TypeInfo(TRawUTF8DynArray));
end;

{ TBHManager }

procedure TBHManager.SetStatus(AValue: TBHManagerStatus);
begin
  if FStatus = AValue then
    Exit;
  FStatus := AValue;
  if Assigned(OnStatusChange) then
    OnStatusChange(Self);
end;

function TBHManager.Init: TBHErrorKind;
begin
  Result := bekNone;
  FreeAndNil(FProvider);
  FProvider := MakeProvider(False);
  if Provider is TBHGaiaProvider then
    if not TBHGaiaProvider(FProvider).Hub.Prepare then
      Result := bekUnavailableProvider;
  if Result = bekNone then
  begin
    FLinkShortener := TBHLinkShortener.Create(Self);
    Result := FLinkShortener.Prepare;
  end;
  if Result = bekNone then
    SetStatus(bhmsReady);
end;

procedure TBHManager.SetOptions(AValue: TBHManagerOptions);
begin
  if FOptions = AValue then
    Exit;
  FOptions := AValue;
  {$IFNDEF BH_ENABLE_TESTHUB}
  FOptions -= [bmoTestHub];
  {$ENDIF}
  {$IFNDEF BH_ENABLE_NOENCRYPTION}
  FOptions -= [bmoNoEncryption];
  {$ENDIF}
  {$IFNDEF BH_ENABLE_LOCALSTORAGE}
  FOptions -= [bmoLocalStorage];
  {$ENDIF}
  {$IFNDEF BH_ENABLE_DEFLATEFILE}
  FOptions -= [bmoNoFileCompression];
  {$ENDIF}
end;

function TBHManager.GetInfoStorageName: TFileName;
begin
  Result := GetAppConfigDir(False) + '.storage';
end;

function TBHManager.GetIsStorageValid: boolean;
begin
  Result := LoadInfo(True);
end;

function TBHManager.LoadInfo(AJustCheck: boolean): boolean;
var
  Data: RawByteString;
  Storage: TBHManagerInfoStorage;
begin
  Result := FileExists(InfoStorageName);
  if not Result then
    Exit;
  Storage := TBHManagerInfoStorage.Create;
  Data := CryptDataForCurrentUser(StringFromFile(InfoStorageName), ExeVersion.User, False);
  try
    JSONToObject(Storage, Pointer(Data), Result);
    if not Result then
      Exit;
    with Storage do
      Result := (Version in [4, 5]) and (PrivateKey <> '') and (DeviceID <> '');
    if not Result then
      Exit;
    if AJustCheck then
      Exit;
    try
      FAuth.PrivateKey := TCrypto.StringToPrivateKey(Storage.PrivateKey);
      FDeviceID := Storage.DeviceID;
    except
      Result := False;
    end;
  finally
    Storage.Free;
    FillZero(Data);
  end;
end;

function TBHManager.SaveInfo: boolean;
var
  Storage: TBHManagerInfoStorage;
  Data: RawUTF8;
begin
  Storage := TBHManagerInfoStorage.Create;
  try
    Storage.Version := BH_VERSION;
    Storage.PrivateKey := TCrypto.PrivateKeyAsString(FAuth.PrivateKey);
    Storage.DeviceID := DeviceID;
    Data := ObjectToJSON(Storage);
    Data := CryptDataForCurrentUser(Data, ExeVersion.User, True);
    Result := FileFromString(Data, InfoStorageName);
  finally
    Storage.Free;
    FillZero(Data);
  end;
end;

function TBHManager.ClearInfo: boolean;
begin
  Result := DeleteFile(GetInfoStorageName);
end;

function TBHManager.MakeProvider(ARandom: boolean): TBHProvider;
begin
  if ARandom then
  begin
    if bmoLocalStorage in FOptions then
      Result := TBHLocalProvider.Create(TAESPRNG.Main.FillRandomHex(8))
    else if bmoTestHub in FOptions then
      Result := MakeGaiaProvider(BHTestGaiaURL, TCrypto.GeneratePrivateKey)
    else
      Result := MakeGaiaProvider(Auth.HubURL, TCrypto.GeneratePrivateKey);
  end
  else
  begin
    if bmoLocalStorage in FOptions then
      Result := TBHLocalProvider.Create('User')
    else if bmoTestHub in FOptions then
      Result := MakeGaiaProvider(BHTestGaiaURL, Auth.PrivateKey)
    else
      Result := MakeGaiaProvider(Auth.HubURL, Auth.PrivateKey);
  end;
end;

function TBHManager.MakeGaiaProvider(AHost: RawUTF8; APrivateKey: IECPrivateKeyParameters): TBHGaiaProvider;
var
  Hub: TGaiaHub;
begin
  Hub := TGaiaHub.Create;
  with Hub do
  begin
    PrivateKey := APrivateKey;
    Host := AHost;
  end;
  Result := TBHGaiaProvider.Create(Hub, True);
end;

procedure TBHManager.DoUpload(ARequest: TBHShareRequest);
begin
  FCurrentRequest := ARequest;
  if Assigned(OnUploadChange) then
    OnUploadChange(Self, ARequest);
  TThread.ExecuteInThread(@ARequest.Run);
end;

procedure TBHManager.UpdateUpload(ARequest: TBHShareRequest);
begin
  if ARequest <> FCurrentRequest then
    Exit;
  case ARequest.Share.State of
    bssPending: ;
    bssInitializing: SetStatus(bhmsStartingUpload);
    bssRunning: SetStatus(bhmsUploading);
    bssPaused: ;
    bssStoped:
    begin
      if ARequest.Share.Error <> bekNone then
        SetStatus(bhmsUploadError);
      SetStatus(bhmsReady);
    end;
    bssFinished: SetStatus(bhmsReady);
  end;
  if Assigned(OnUploadChange) then
    OnUploadChange(Self, ARequest);
end;

function TBHManager.BlockStackErrorToBHError(AValue: TBlockStackErrorKind): TBHErrorKind;
const
  Er: array[TBlockStackErrorKind] of TBHErrorKind =
    (bekNone, bekUnknown, bekInvalidInputPrivateKey, bekInvalidResponse,
    bekMultiPublicKeys,
    bekInvalidSignature, bekInvalidAddress, bekInvalidUserName, bekInvalidPrivateKey);
begin
  Result := Er[AValue];
end;

function TBHManager.Encrypt(const AKey: RawUTF8; const AInput: RawByteString; ALength: integer; out AOutput: RawByteString): boolean;
begin
  if bmoNoEncryption in FOptions then
  begin
    Result := True;
    SetString(AOutput, @AInput[1], ALength);
  end
  else
    Result := TCrypto.Encrypt(AKey, AInput, ALength, AOutput);
end;

function TBHManager.Encrypt(const AKey: RawUTF8; const AInput: RawByteString; out AOutput: RawByteString): boolean;
begin
  Result := Encrypt(AKey, AInput, Length(AInput), AOutput);
end;

function TBHManager.Decrypt(const AKey: RawUTF8; const AInput: RawByteString; out AOutput: RawByteString): boolean;
begin
  if bmoNoEncryption in FOptions then
  begin
    Result := True;
    AOutput := AInput;
  end
  else
    Result := TCrypto.Decrypt(AKey, AInput, AOutput);
end;

function TBHManager.Encrypt(const AInput: RawByteString; out AOutput: RawByteString): boolean;
begin
  if bmoNoEncryption in FOptions then
  begin
    Result := True;
    AOutput := AInput;
  end
  else
    Result := TCrypto.Encrypt(FAuth.PublicKey, AInput, AOutput);
end;

function TBHManager.Decrypt(const AInput: RawByteString; out AOutput: RawByteString): boolean;
begin
  if bmoNoEncryption in FOptions then
  begin
    Result := True;
    AOutput := AInput;
  end
  else
    Result := TCrypto.Decrypt(FAuth.PrivateKey, AInput, AOutput);
end;

constructor TBHManager.Create(AOptions: TBHManagerOptions);
begin
  SetOptions(AOptions);
  FAuth := TBlockStack.Create;
  FPrepared := False;
  SetStatus(bhmsNone);
end;

destructor TBHManager.Destroy;
begin
  SetStatus(bhmsNone);
  FAuth.Free;
  FProvider.Free;
  FLinkShortener.Free;
  inherited Destroy;
end;

function TBHManager.Prepare: TBHErrorKind;
begin
  if LoadInfo(False) then
    Result := Init
  else
  begin
    ClearInfo;
    Result := bekNeedAuthentication;
    SetStatus(bhmsNeedAuthentication);
    FDeviceID := TAESPRNG.Main.FillRandomHex(4);
    SignInPrivateKey := TCrypto.GeneratePrivateKey;
    OnSignInRequest(Self, FAuth.GenerateSignInURL(BH_SIGNIN_REDIRECT_URL, BH_MANIFEST_URL, BH_DOMAIN, SignInPrivateKey));
  end;
  FPrepared := Result = bekNone;
end;

function TBHManager.Clear: boolean;
begin
  Result := ClearInfo;
end;

function TBHManager.HandleSignInResponse(const AResponse: RawUTF8): TBHErrorKind;
begin
  Result := BlockStackErrorToBHError(FAuth.HandleSignInResponse(AResponse, SignInPrivateKey));
  if Result = bekNone then
    if not SaveInfo then
      Result := bekCanNotMakeStorageFile;
end;

function TBHManager.Add(ARequest: TBHShareRequest): integer;
begin
  if Status <> bhmsReady then
    Exit(-1);
  Result := 0;
  DoUpload(ARequest);
end;

function TBHManager.Stop(ARequest: TBHShareRequest): boolean;
begin
  if ARequest.Share.State = bssStoped then
    Exit(False);
  ARequest.Share.State := bssStoped;
  if ARequest = FCurrentRequest then
  begin
    SetStatus(bhmsReady);
    FCurrentRequest := nil;
  end;
  Result := True;
end;

function TBHManager.GetShareFullURL(AShare: TBHShare): RawUTF8;
begin
  if AShare.Error <> bekNone then
    Exit('');
  if bmoTestHub in FOptions then
  begin
    if (AShare.ShortURL <> '') then
      Result := BHTestShareURL + AShare.ShortURL
    else
      Result := BHTestShareURL + AShare.URL;
  end
  else
  if (AShare.ShortURL <> '') then
    Result := BH_SHARE_URL + AShare.ShortURL
  else
    Result := BH_SHARE_URL + AShare.URL;
end;

end.
