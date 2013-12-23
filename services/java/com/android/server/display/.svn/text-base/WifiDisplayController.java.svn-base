/*
 * Copyright (C) 2012 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.android.server.display;

import com.android.internal.util.DumpUtils;

import android.content.BroadcastReceiver;
import android.content.ContentResolver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.database.ContentObserver;
import android.hardware.display.WifiDisplay;
import android.hardware.display.WifiDisplayStatus;
import android.media.AudioManager;
import android.media.RemoteDisplay;
import android.net.NetworkInfo;
import android.net.Uri;
import android.net.wifi.WpsInfo;
import android.net.wifi.p2p.WifiP2pConfig;
import android.net.wifi.p2p.WifiP2pDevice;
import android.net.wifi.p2p.WifiP2pDeviceList;
import android.net.wifi.p2p.WifiP2pGroup;
import android.net.wifi.p2p.WifiP2pManager;
import android.net.wifi.p2p.WifiP2pWfdInfo;
import android.net.wifi.p2p.WifiP2pManager.ActionListener;
import android.net.wifi.p2p.WifiP2pManager.Channel;
import android.net.wifi.p2p.WifiP2pManager.GroupInfoListener;
import android.net.wifi.p2p.WifiP2pManager.PeerListListener;
import android.os.Handler;
import android.provider.Settings;
import android.util.Slog;
import android.view.Surface;

import java.io.PrintWriter;
import java.net.Inet4Address;
import java.net.InetAddress;
import java.net.NetworkInterface;
import java.net.SocketException;
import java.util.ArrayList;
import java.util.Enumeration;

import libcore.util.Objects;

///M:@{
import android.app.AlertDialog;
import android.bluetooth.BluetoothAdapter;
import android.content.DialogInterface;
import android.content.DialogInterface.OnClickListener;
import android.content.res.Resources;
import android.hardware.input.InputManager;
import android.net.wifi.WifiManager;
import android.net.wifi.WifiManager.WifiLock;
import android.net.wifi.p2p.wfd.WfdLinkInfo;
import android.net.wifi.p2p.WifiP2pManager.WfdLinkInfoListener;
import android.net.wifi.p2p.WifiP2pWfdInfo;
import android.os.Message;
import android.os.SystemClock;
import android.os.SystemProperties;
import android.os.UserHandle;
import android.util.DisplayMetrics;
import android.view.InputDevice;
import android.view.KeyCharacterMap;
import android.view.KeyEvent;
import android.view.MotionEvent;
import android.view.WindowManager;
import android.view.WindowManagerPolicy;
import android.widget.Toast;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.util.regex.Pattern;
import java.util.regex.Matcher;

import com.android.internal.R;
import com.mediatek.common.featureoption.FeatureOption;
import com.mediatek.common.hdmi.IHDMINative;
import com.mediatek.common.MediatekClassFactory;
import android.database.ContentObserver;
import android.provider.Settings;
import android.net.Uri;
import android.os.Handler;
import android.app.Notification;
import android.app.Notification.Builder;
import android.app.NotificationManager;

///@}


/**
 * Manages all of the various asynchronous interactions with the {@link WifiP2pManager}
 * on behalf of {@link WifiDisplayAdapter}.
 * <p>
 * This code is isolated from {@link WifiDisplayAdapter} so that we can avoid
 * accidentally introducing any deadlocks due to the display manager calling
 * outside of itself while holding its lock.  It's also way easier to write this
 * asynchronous code if we can assume that it is single-threaded.
 * </p><p>
 * The controller must be instantiated on the handler thread.
 * </p>
 */
final class WifiDisplayController implements DumpUtils.Dump {
    private static final String TAG = "WifiDisplayController";
    private static boolean DEBUG = false;

    private static final int DEFAULT_CONTROL_PORT = 7236;
    private static final int MAX_THROUGHPUT = 50;
    private static final int CONNECTION_TIMEOUT_SECONDS = 60;
    /// M: Modify for speed up rtsp setup
    private static final int RTSP_TIMEOUT_SECONDS = 15 + CONNECTION_TIMEOUT_SECONDS;

    private static final int DISCOVER_PEERS_MAX_RETRIES = 10;
    private static final int DISCOVER_PEERS_RETRY_DELAY_MILLIS = 500;

    private static final int CONNECT_MAX_RETRIES = 3;
    private static final int CONNECT_RETRY_DELAY_MILLIS = 500;

    // A unique token to identify the remote submix that is managed by Wifi display.
    // It must match what the media server uses when it starts recording the submix
    // for transmission.  We use 0 although the actual value is currently ignored.
    private static final int REMOTE_SUBMIX_ADDRESS = 0;

    private final Context mContext;
    private final Handler mHandler;
    private final Listener mListener;

    private final WifiP2pManager mWifiP2pManager;
    private final Channel mWifiP2pChannel;

    private final AudioManager mAudioManager;

    private boolean mWifiP2pEnabled;
    private boolean mWfdEnabled;
    private boolean mWfdEnabling;
    private NetworkInfo mNetworkInfo;

    private final ArrayList<WifiP2pDevice> mAvailableWifiDisplayPeers =
            new ArrayList<WifiP2pDevice>();

    // True if Wifi display is enabled by the user.
    private boolean mWifiDisplayOnSetting;

    // True if there is a call to discoverPeers in progress.
    private boolean mDiscoverPeersInProgress;

    // Number of discover peers retries remaining.
    private int mDiscoverPeersRetriesLeft;

    // The device to which we want to connect, or null if we want to be disconnected.
    private WifiP2pDevice mDesiredDevice;

    // The device to which we are currently connecting, or null if we have already connected
    // or are not trying to connect.
    private WifiP2pDevice mConnectingDevice;

    // The device from which we are currently disconnecting.
    private WifiP2pDevice mDisconnectingDevice;

    // The device to which we were previously trying to connect and are now canceling.
    private WifiP2pDevice mCancelingDevice;

    // The device to which we are currently connected, which means we have an active P2P group.
    private WifiP2pDevice mConnectedDevice;

    // The group info obtained after connecting.
    private WifiP2pGroup mConnectedDeviceGroupInfo;

    // Number of connection retries remaining.
    private int mConnectionRetriesLeft;

    // The remote display that is listening on the connection.
    // Created after the Wifi P2P network is connected.
    private RemoteDisplay mRemoteDisplay;

    // The remote display interface.
    private String mRemoteDisplayInterface;

    // True if RTSP has connected.
    private boolean mRemoteDisplayConnected;

    // True if the remote submix is enabled.
    private boolean mRemoteSubmixOn;

    // The information we have most recently told WifiDisplayAdapter about.
    private WifiDisplay mAdvertisedDisplay;
    private Surface mAdvertisedDisplaySurface;
    private int mAdvertisedDisplayWidth;
    private int mAdvertisedDisplayHeight;
    private int mAdvertisedDisplayFlags;

    ///M:@{
    private int mBackupShowTouchVal;
    private boolean mFast_NeedFastRtsp;
    private String mFast_DesiredMac;
    //private int mBackupScreenOffTimeout;
    private boolean mIsNeedRotate;
    private boolean mIsConnected_OtherP2p;
    private boolean mIsConnecting_P2p_Rtsp;
    private static final int CONNECT_MIN_RETRIES = 0;

    // for BT/WFD exclude
    private boolean mBTOnSetting;    
    private BluetoothAdapter mBTAdapter;
    private final static int WFDCONTROLLER_WFD_UPDATE = 0;
    private final static int WFDCONTROLLER_BT_UPDATE = 1;
    private final static int WFDCONTROLLER_HDMI_UPDATE = 2;

    // for HDMI/WFD exclude
    private boolean mHDMIOnSetting;
    private IHDMINative mHdmiNative;
    public static final String WFDCONTROLLER_HDMI_ENABLE_CONFIG = "hdmi_enable_status";

    // for Wfd stat file
    private final static String WFDCONTROLLER_WFD_STAT_FILE = "/proc/wmt_tm/wfd_stat";
    private final static int WFDCONTROLLER_WFD_STAT_DISCONNECT = 0;
    private final static int WFDCONTROLLER_WFD_STAT_STANDBY = 1;
    private final static int WFDCONTROLLER_WFD_STAT_STREAMING = 2;

    // for WFD connected/disconnected
    public static final String WFD_CONNECTION = "com.mediatek.wfd.connection";
    private boolean mIsWFDConnected;

    // for DRM content on media player
    public static final String DRM_CONTENT_MEDIAPLAYER = "com.mediatek.mediaplayer.DRM_PLAY";
    private boolean mDRMContent_Mediaplayer;
    private int mPlayerID_Mediaplayer;

    // for wifi link info
    private final static int WFDCONTROLLER_LINK_INFO_PERIOD_MILLIS = 2*1000;

    // for quality enhancement
    private final static int WFDCONTROLLER_SCORE_THRESHOLD1 = 100;
    private final static int WFDCONTROLLER_SCORE_THRESHOLD2 = 80;
    private final static int WFDCONTROLLER_SCORE_THRESHOLD3 = 30;
    private final static int WFDCONTROLLER_SCORE_THRESHOLD4 = 10;
    private int WFDCONTROLLER_DISPLAY_TOAST_TIME;  
    private int WFDCONTROLLER_DISPLAY_NOTIFICATION_TIME;  
    private boolean WFDCONTROLLER_SQC_INFO_ON = false;
    private boolean WFDCONTROLLER_QE_ON = true; 

    private final static int WFDCONTROLLER_AVERATE_SCORE_COUNT = 4;  
    private final static int WFDCONTROLLER_INVALID_VALUE = -1;    
    private int[] mScore = new int[WFDCONTROLLER_AVERATE_SCORE_COUNT];
    private int mScoreIndex = 0;

    private int mScoreLevel = 0;
    private int mLevel = 0;
    private final NotificationManager mNotificationManager;
    private boolean mNotiTimerStarted;
    private boolean mToastTimerStarted;

    // ALPS00677009: for reconnect
    private WifiP2pDevice mReConnectDevice;
    private static final int RECONNECT_RETRY_DELAY_MILLIS = 1000;
    private int mReConnection_Timeout_Remain_Seconds;
    private boolean mReConnecting;
    
    // ALPS00759126: keep wifi enabled when WFD connected
    private WifiLock mWifiLock;
    private WifiManager mWifiManager;

    // ALPS00772074: do disconnect for every power-off case
    private final static String WFDCONTROLLER_PRE_SHUTDOWN = "android.intent.action.ACTION_PRE_SHUTDOWN";
    
    // ALPS00812236: dismiss all dialogs when wifi p2p/wfd is disabled
    private final static int WFD_WIFIP2P_EXCLUDED_DIALOG = 1;
    private final static int WFD_BT_EXCLUDED_DIALOG = 2;
    private final static int WFD_HDMI_EXCLUDED_DIALOG_WFD_UPDATE = 3;
    private final static int WFD_HDMI_EXCLUDED_DIALOG_HDMI_UPDATE = 4;
    private final static int WFD_RECONNECT_DIALOG = 5;
    private AlertDialog mWifiDirectExcludeDialog;
    private AlertDialog mBTExcludeDialog;
    private AlertDialog mHDMIExcludeDialog_WfdUpdate;
    private AlertDialog mHDMIExcludeDialog_HDMIUpdate;
    private AlertDialog mReConnecteDialog;
    private boolean mUserDecided;
    ///@}


    public WifiDisplayController(Context context, Handler handler, Listener listener) {
        mContext = context;
        mHandler = handler;
        mListener = listener;

        mWifiP2pManager = (WifiP2pManager)context.getSystemService(Context.WIFI_P2P_SERVICE);
        mWifiP2pChannel = mWifiP2pManager.initialize(context, handler.getLooper(), null);

        mAudioManager = (AudioManager)context.getSystemService(Context.AUDIO_SERVICE);

        IntentFilter intentFilter = new IntentFilter();
        intentFilter.addAction(WifiP2pManager.WIFI_P2P_STATE_CHANGED_ACTION);
        intentFilter.addAction(WifiP2pManager.WIFI_P2P_PEERS_CHANGED_ACTION);
        intentFilter.addAction(WifiP2pManager.WIFI_P2P_CONNECTION_CHANGED_ACTION);
        ///M:@{
        intentFilter.addAction(DRM_CONTENT_MEDIAPLAYER);
        intentFilter.addAction(WifiP2pManager.WIFI_P2P_DISCOVERY_CHANGED_ACTION);
        intentFilter.addAction(BluetoothAdapter.ACTION_STATE_CHANGED);
        intentFilter.addAction(WFDCONTROLLER_PRE_SHUTDOWN);
        ///@}
        context.registerReceiver(mWifiP2pReceiver, intentFilter, null, mHandler);

        ContentObserver settingsObserver = new ContentObserver(mHandler) {
            @Override
            public void onChange(boolean selfChange, Uri uri) {
                updateSettings();
            }
        };

        final ContentResolver resolver = mContext.getContentResolver();
        resolver.registerContentObserver(Settings.Global.getUriFor(
                Settings.Global.WIFI_DISPLAY_ON), false, settingsObserver);
        updateSettings();

        ///M:@{
        //observe HDMI
        ContentObserver settingsObserverHDMI = new ContentObserver(mHandler) {
            @Override
            public void onChange(boolean selfChange, Uri uri) {
                updateSettingsHDMI();
            }
        };

        resolver.registerContentObserver(Settings.System.getUriFor(
                WFDCONTROLLER_HDMI_ENABLE_CONFIG), false, settingsObserverHDMI);

        DisplayMetrics dm = new DisplayMetrics();
        dm = mContext.getResources().getDisplayMetrics();
        Slog.i(TAG, "DisplayMetrics, Width = " + dm.widthPixels + ", Height = " + dm.heightPixels);
        if (dm.widthPixels < dm.heightPixels) {
            mIsNeedRotate = true;
        }
        //reset all Setting config 
        actionAtDisconnected(null);
        updateWfdStatFile(WFDCONTROLLER_WFD_STAT_DISCONNECT);
        mWifiP2pManager.setWfdSessionMode(mWifiP2pChannel, WifiP2pWfdInfo.DISCONNECTED, null);
        
        // Register EM observer
        registerEMObserver();

        mNotificationManager = (NotificationManager)context.getSystemService(
                Context.NOTIFICATION_SERVICE);

        //get WiFi lock
        getWifiLock();
        ///@}
        
    }

    private void updateSettings() {
        final ContentResolver resolver = mContext.getContentResolver();
        mWifiDisplayOnSetting = Settings.Global.getInt(resolver,
                Settings.Global.WIFI_DISPLAY_ON, 0) != 0;

        ///M:@{
        loadDebugLevel();
        if (!FeatureOption.MTK_HDMI_SUPPORT) {
            mHDMIOnSetting = false;
        } else {
            mHDMIOnSetting = Settings.System.getInt(resolver,
                WFDCONTROLLER_HDMI_ENABLE_CONFIG, 1) != 0;
        }

        if (true==mWifiDisplayOnSetting && true==mBTOnSetting) {
            String btExclude = SystemProperties.get("wlan.wfd.bt.exclude", "1");
            if (0 != Integer.valueOf(btExclude)) {
                dialogWfdBtConflict(WFDCONTROLLER_WFD_UPDATE);
            } else {
                updateWfdEnableState();
            }

        } else if (true==mWifiDisplayOnSetting && true==mHDMIOnSetting) {
            dialogWfdHdmiConflict(WFDCONTROLLER_WFD_UPDATE);

        } else {
            updateWfdEnableState();

        }
        ///@}
    }

    @Override
    public void dump(PrintWriter pw) {
        pw.println("mWifiDisplayOnSetting=" + mWifiDisplayOnSetting);
        pw.println("mWifiP2pEnabled=" + mWifiP2pEnabled);
        pw.println("mWfdEnabled=" + mWfdEnabled);
        pw.println("mWfdEnabling=" + mWfdEnabling);
        pw.println("mNetworkInfo=" + mNetworkInfo);
        pw.println("mDiscoverPeersInProgress=" + mDiscoverPeersInProgress);
        pw.println("mDiscoverPeersRetriesLeft=" + mDiscoverPeersRetriesLeft);
        pw.println("mDesiredDevice=" + describeWifiP2pDevice(mDesiredDevice));
        pw.println("mConnectingDisplay=" + describeWifiP2pDevice(mConnectingDevice));
        pw.println("mDisconnectingDisplay=" + describeWifiP2pDevice(mDisconnectingDevice));
        pw.println("mCancelingDisplay=" + describeWifiP2pDevice(mCancelingDevice));
        pw.println("mConnectedDevice=" + describeWifiP2pDevice(mConnectedDevice));
        pw.println("mConnectionRetriesLeft=" + mConnectionRetriesLeft);
        pw.println("mRemoteDisplay=" + mRemoteDisplay);
        pw.println("mRemoteDisplayInterface=" + mRemoteDisplayInterface);
        pw.println("mRemoteDisplayConnected=" + mRemoteDisplayConnected);
        pw.println("mRemoteSubmixOn=" + mRemoteSubmixOn);
        pw.println("mAdvertisedDisplay=" + mAdvertisedDisplay);
        pw.println("mAdvertisedDisplaySurface=" + mAdvertisedDisplaySurface);
        pw.println("mAdvertisedDisplayWidth=" + mAdvertisedDisplayWidth);
        pw.println("mAdvertisedDisplayHeight=" + mAdvertisedDisplayHeight);
        pw.println("mAdvertisedDisplayFlags=" + mAdvertisedDisplayFlags);
        ///M:@{
        pw.println("mBackupShowTouchVal=" + mBackupShowTouchVal);
        pw.println("mFast_NeedFastRtsp=" + mFast_NeedFastRtsp);
        pw.println("mFast_DesiredMac=" + mFast_DesiredMac);
        pw.println("mIsNeedRotate=" + mIsNeedRotate);
        pw.println("mIsConnected_OtherP2p=" + mIsConnected_OtherP2p);
        pw.println("mIsConnecting_P2p_Rtsp=" + mIsConnecting_P2p_Rtsp);
        pw.println("mBTOnSetting=" + mBTOnSetting);
        pw.println("mHDMIOnSetting=" + mHDMIOnSetting);
        pw.println("mIsWFDConnected=" + mIsWFDConnected);
        pw.println("mDRMContent_Mediaplayer=" + mDRMContent_Mediaplayer);
        pw.println("mPlayerID_Mediaplayer=" + mPlayerID_Mediaplayer);
        ///@}
        pw.println("mAvailableWifiDisplayPeers: size=" + mAvailableWifiDisplayPeers.size());
        for (WifiP2pDevice device : mAvailableWifiDisplayPeers) {
            pw.println("  " + describeWifiP2pDevice(device));
        }
    }

    public void requestScan() {
        Slog.i(TAG, Thread.currentThread().getStackTrace()[2].getMethodName());
        discoverPeers();
    }

    public void requestConnect(String address) {
        Slog.i(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() + ", address = " + address);
        ///M:@{
        if (mIsConnected_OtherP2p) {
            showDialog(WFD_WIFIP2P_EXCLUDED_DIALOG);

        } else {
            if (DEBUG) {
                Slog.d(TAG, "mAvailableWifiDisplayPeers dump:");
            }

            for (WifiP2pDevice device : mAvailableWifiDisplayPeers) {
                if (DEBUG) {
                    Slog.d(TAG, "\t" + describeWifiP2pDevice(device));
                }
                if (device.deviceAddress.equals(address)) {
                    connect(device);
                }
            }

        }
        ///@}
    }

    public void requestDisconnect() {
        Slog.i(TAG, Thread.currentThread().getStackTrace()[2].getMethodName());
        disconnect();
    }

    private void updateWfdEnableState() {
        if (mWifiDisplayOnSetting && mWifiP2pEnabled) {
            // WFD should be enabled.
            if (!mWfdEnabled && !mWfdEnabling) {
                mWfdEnabling = true;

                WifiP2pWfdInfo wfdInfo = new WifiP2pWfdInfo();
                wfdInfo.setWfdEnabled(true);
                wfdInfo.setDeviceType(WifiP2pWfdInfo.WFD_SOURCE);
                wfdInfo.setSessionAvailable(true);
                wfdInfo.setControlPort(DEFAULT_CONTROL_PORT);
                wfdInfo.setMaxThroughput(MAX_THROUGHPUT);
                mWifiP2pManager.setWFDInfo(mWifiP2pChannel, wfdInfo, new ActionListener() {
                    @Override
                    public void onSuccess() {
                        if (DEBUG) {
                            Slog.d(TAG, "Successfully set WFD info.");
                        }
                        if (mWfdEnabling) {
                            mWfdEnabling = false;
                            mWfdEnabled = true;
                            reportFeatureState();
                        }
                    }

                    @Override
                    public void onFailure(int reason) {
                        if (DEBUG) {
                            Slog.d(TAG, "Failed to set WFD info with reason " + reason + ".");
                        }
                        mWfdEnabling = false;
                    }
                });
            }
        } else {
            // WFD should be disabled.
            mWfdEnabling = false;
            mWfdEnabled = false;
            reportFeatureState();
            disconnect();
            ///M:@{
            WifiP2pWfdInfo wfdInfo = new WifiP2pWfdInfo();
            wfdInfo.setWfdEnabled(false);
            mWifiP2pManager.setWFDInfo(mWifiP2pChannel, wfdInfo, null);
            // ALPS00812236: dismiss all dialogs when wfd is disabled
            dismissDialog();            
            ///@}            
        }
    }

    private void reportFeatureState() {
        final int featureState = computeFeatureState();
        mHandler.post(new Runnable() {
            @Override
            public void run() {
                Slog.d(TAG, "callback onFeatureStateChanged(): featureState = " + featureState);
                mListener.onFeatureStateChanged(featureState);
            }
        });
    }

    private int computeFeatureState() {
        if (!mWifiP2pEnabled) {
            return WifiDisplayStatus.FEATURE_STATE_DISABLED;
        }
        return mWifiDisplayOnSetting ? WifiDisplayStatus.FEATURE_STATE_ON :
                WifiDisplayStatus.FEATURE_STATE_OFF;
    }

    private void discoverPeers() {
        if (!mDiscoverPeersInProgress) {
            mDiscoverPeersInProgress = true;
            mDiscoverPeersRetriesLeft = DISCOVER_PEERS_MAX_RETRIES;
            handleScanStarted();
            tryDiscoverPeers();
        }
    }

    private void tryDiscoverPeers() {
        mWifiP2pManager.discoverPeers(mWifiP2pChannel, new ActionListener() {
            @Override
            public void onSuccess() {
                if (DEBUG) {
                    Slog.d(TAG, "Discover peers succeeded.  Requesting peers now.");
                }

                mDiscoverPeersInProgress = false;
                requestPeers();
            }

            @Override
            public void onFailure(int reason) {
                if (DEBUG) {
                    Slog.d(TAG, "Discover peers failed with reason " + reason + ".");
                }

                if (mDiscoverPeersInProgress) {
                    if (reason == 0 && mDiscoverPeersRetriesLeft > 0 && mWfdEnabled) {
                        mHandler.postDelayed(new Runnable() {
                            @Override
                            public void run() {
                                if (mDiscoverPeersInProgress) {
                                    if (mDiscoverPeersRetriesLeft > 0 && mWfdEnabled) {
                                        mDiscoverPeersRetriesLeft -= 1;
                                        if (DEBUG) {
                                            Slog.d(TAG, "Retrying discovery.  Retries left: "
                                                    + mDiscoverPeersRetriesLeft);
                                        }
                                        tryDiscoverPeers();
                                    } else {
                                        handleScanFinished();
                                        mDiscoverPeersInProgress = false;
                                    }
                                }
                            }
                        }, DISCOVER_PEERS_RETRY_DELAY_MILLIS);
                    } else {
                        handleScanFinished();
                        mDiscoverPeersInProgress = false;
                    }
                }
            }
        });
    }

    private void requestPeers() {
        mWifiP2pManager.requestPeers(mWifiP2pChannel, new PeerListListener() {
            @Override
            public void onPeersAvailable(WifiP2pDeviceList peers) {
                if (DEBUG) {
                    Slog.d(TAG, "Received list of peers.");
                }

                mAvailableWifiDisplayPeers.clear();
                for (WifiP2pDevice device : peers.getDeviceList()) {
                    if (DEBUG) {
                        Slog.d(TAG, "  " + describeWifiP2pDevice(device));
                    }

                    ///M:@{
                    if (null!=mConnectedDevice &&
                        mConnectedDevice.deviceAddress.equals(device.deviceAddress)) {
                        mAvailableWifiDisplayPeers.add(device);
                    } else 
                    ///@}
                    if (isWifiDisplay(device)) {
                        mAvailableWifiDisplayPeers.add(device);
                    }
                }

                    handleScanFinished();
                }
        });
    }

    private void handleScanStarted() {
        mHandler.post(new Runnable() {
            @Override
            public void run() {
                Slog.d(TAG, "callback onScanStarted()");
                mListener.onScanStarted();
            }
        });
    }

    private void handleScanFinished() {
        final int count = mAvailableWifiDisplayPeers.size();
        final WifiDisplay[] displays = WifiDisplay.CREATOR.newArray(count);
        for (int i = 0; i < count; i++) {
            WifiP2pDevice device = mAvailableWifiDisplayPeers.get(i);
            displays[i] = createWifiDisplay(device);
            updateDesiredDevice(device);
        }

        mHandler.post(new Runnable() {
            @Override
            public void run() {
                Slog.d(TAG, "callback onScanFinished(), count = " + count);
                if (DEBUG) {
                    for (int i = 0; i < count; i++) {
                        Slog.d(TAG, "\t" + displays[i].getDeviceName() + ": " + displays[i].getDeviceAddress());
                    }
                }

                mListener.onScanFinished(displays);
            }
        });
    }

    private void updateDesiredDevice(WifiP2pDevice device) {
        // Handle the case where the device to which we are connecting or connected
        // may have been renamed or reported different properties in the latest scan.
        final String address = device.deviceAddress;
        if (mDesiredDevice != null && mDesiredDevice.deviceAddress.equals(address)) {
            if (DEBUG) {
                Slog.d(TAG, "updateDesiredDevice: new information "
                        + describeWifiP2pDevice(device));
            }
            mDesiredDevice.update(device);
            if (mAdvertisedDisplay != null
                    && mAdvertisedDisplay.getDeviceAddress().equals(address)) {
                readvertiseDisplay(createWifiDisplay(mDesiredDevice));
            }
        }
    }

    private void connect(final WifiP2pDevice device) {
        Slog.i(TAG, "connect: device name = " + device.deviceName);
        if (mDesiredDevice != null
                && !mDesiredDevice.deviceAddress.equals(device.deviceAddress)) {
            if (DEBUG) {
                Slog.d(TAG, "connect: nothing to do, already connecting to "
                        + describeWifiP2pDevice(mDesiredDevice));    ///Modified by MTK
            }
            return;
        }

        ///M:@{ ALPS00792267: avoid to connect the same dongle rapidly*/
        if (mDesiredDevice != null
                && mDesiredDevice.deviceAddress.equals(device.deviceAddress)) {
            if (DEBUG) {
                Slog.d(TAG, "connect: connecting to the same dongle already "
                        + describeWifiP2pDevice(mDesiredDevice));
            }
            return;
        }
        ///@}

        if (mConnectedDevice != null
                && !mConnectedDevice.deviceAddress.equals(device.deviceAddress)
                && mDesiredDevice == null) {
            if (DEBUG) {
                Slog.d(TAG, "connect: nothing to do, already connected to "
                        + describeWifiP2pDevice(device) + " and not part way through "
                        + "connecting to a different device.");
            }
            return;
        }

        mDesiredDevice = device;
        mConnectionRetriesLeft = CONNECT_MIN_RETRIES;   ///Modify by MTK
        updateConnection();
    }

    private void disconnect() {
        Slog.i(TAG, "disconnect, mRemoteDisplayInterface = " + mRemoteDisplayInterface);
        mDesiredDevice = null;
        ///M:@{
        updateWfdStatFile(WFDCONTROLLER_WFD_STAT_DISCONNECT);
        if (null != mConnectedDevice) {
            mReConnectDevice = mConnectedDevice;
        }
        ///@}
        updateConnection();
    }

    private void retryConnection() {
        // Cheap hack.  Make a new instance of the device object so that we
        // can distinguish it from the previous connection attempt.
        // This will cause us to tear everything down before we try again.
        mDesiredDevice = new WifiP2pDevice(mDesiredDevice);
        updateConnection();
    }

    /**
     * This function is called repeatedly after each asynchronous operation
     * until all preconditions for the connection have been satisfied and the
     * connection is established (or not).
     */
    private void updateConnection() {
        // Step 1. Before we try to connect to a new device, tell the system we
        // have disconnected from the old one.
        ///M:@{
        //if (mRemoteDisplay != null && mConnectedDevice != mDesiredDevice) {
        if ( (mRemoteDisplay != null && mConnectedDevice != mDesiredDevice) ||
             (true == mIsConnecting_P2p_Rtsp) ) {
            String localInterface = (null!=mRemoteDisplayInterface) ? mRemoteDisplayInterface : "localhost";
            String localDeviceName = (null!=mConnectedDevice) ? mConnectedDevice.deviceName :
                                        ((null!=mConnectingDevice) ? mConnectingDevice.deviceName : "N/A");
            Slog.i(TAG, "Stopped listening for RTSP connection on " + localInterface
                        + " from Wifi display : " + localDeviceName);

            mIsConnected_OtherP2p = false;
            mIsConnecting_P2p_Rtsp = false;
            Slog.i(TAG, "\tbefore dispose() ---> ");
            mListener.onDisplayDisconnecting();
            mRemoteDisplay.dispose();
            Slog.i(TAG, "\t<--- after dispose()");
            ///@}
            mRemoteDisplay = null;
            mRemoteDisplayInterface = null;
            mRemoteDisplayConnected = false;
            mHandler.removeCallbacks(mRtspTimeout);

            setRemoteSubmixOn(false);
            unadvertiseDisplay();

            // continue to next step
        }

        // Step 2. Before we try to connect to a new device, disconnect from the old one.
        if (mDisconnectingDevice != null) {
            return; // wait for asynchronous callback
        }
        if (mConnectedDevice != null && mConnectedDevice != mDesiredDevice) {
            Slog.i(TAG, "Disconnecting from Wifi display: " + mConnectedDevice.deviceName);
            mDisconnectingDevice = mConnectedDevice;
            mConnectedDevice = null;

            unadvertiseDisplay();

            final WifiP2pDevice oldDevice = mDisconnectingDevice;
            mWifiP2pManager.removeGroup(mWifiP2pChannel, new ActionListener() {
                @Override
                public void onSuccess() {
                    Slog.i(TAG, "Disconnected from Wifi display: " + oldDevice.deviceName);
                    next();
                }

                @Override
                public void onFailure(int reason) {
                    Slog.i(TAG, "Failed to disconnect from Wifi display: "
                            + oldDevice.deviceName + ", reason=" + reason);
                    next();
                }

                private void next() {
                    if (mDisconnectingDevice == oldDevice) {
                        mDisconnectingDevice = null;
                        ///M:@{
                        if (null != mRemoteDisplay) {
                            mIsConnecting_P2p_Rtsp = true;
                        }
                        ///@}
                        updateConnection();
                    }
                }
            });
            return; // wait for asynchronous callback
        }

        // Step 3. Before we try to connect to a new device, stop trying to connect
        // to the old one.
        if (mCancelingDevice != null) {
            return; // wait for asynchronous callback
        }
        if (mConnectingDevice != null && mConnectingDevice != mDesiredDevice) {
            Slog.i(TAG, "Canceling connection to Wifi display: " + mConnectingDevice.deviceName);
            mCancelingDevice = mConnectingDevice;
            mConnectingDevice = null;

            unadvertiseDisplay();
            mHandler.removeCallbacks(mConnectionTimeout);

            final WifiP2pDevice oldDevice = mCancelingDevice;
            mWifiP2pManager.cancelConnect(mWifiP2pChannel, new ActionListener() {
                @Override
                public void onSuccess() {
                    Slog.i(TAG, "Canceled connection to Wifi display: " + oldDevice.deviceName);
                    next();
                }

                @Override
                public void onFailure(int reason) {
                    Slog.i(TAG, "Failed to cancel connection to Wifi display: "
                            + oldDevice.deviceName + ", reason=" + reason
                    ///M:@{ ALPS00530805
                    //It may Group been formed but there isn't enough time to notify WFD fwk, and WFD fwk CancelConnect() first.
                            + ". Do removeGroup()");
                    mWifiP2pManager.removeGroup(mWifiP2pChannel, null);
                    ///@}
                    next();
                }

                private void next() {
                    if (mCancelingDevice == oldDevice) {
                        mCancelingDevice = null;
                        ///M:@{
                        if (null != mRemoteDisplay) {
                            mIsConnecting_P2p_Rtsp = true;
                        }
                        ///@}
                        updateConnection();
                    }
                }
            });
            return; // wait for asynchronous callback
        }

        // Step 4. If we wanted to disconnect, then mission accomplished.
        if (mDesiredDevice == null) {
            unadvertiseDisplay();
            return; // done
        }

        // Step 5. Try to connect.
        if (mConnectedDevice == null && mConnectingDevice == null) {
            Slog.i(TAG, "Connecting to Wifi display: " + mDesiredDevice.deviceName);

            mConnectingDevice = mDesiredDevice;
            WifiP2pConfig config = new WifiP2pConfig();
            WpsInfo wps = new WpsInfo();
            if (mConnectingDevice.wpsPbcSupported()) {
                wps.setup = WpsInfo.PBC;
            } else if (mConnectingDevice.wpsDisplaySupported()) {
                // We do keypad if peer does display
                wps.setup = WpsInfo.KEYPAD;
            } else {
                wps.setup = WpsInfo.DISPLAY;
            }
            config.wps = wps;
            config.deviceAddress = mConnectingDevice.deviceAddress;
            // Helps with STA & P2P concurrency
            config.groupOwnerIntent = WifiP2pConfig.MIN_GROUP_OWNER_INTENT;

            WifiDisplay display = createWifiDisplay(mConnectingDevice);
            advertiseDisplay(display, null, 0, 0, 0);

            final WifiP2pDevice newDevice = mDesiredDevice;
            mWifiP2pManager.connect(mWifiP2pChannel, config, new ActionListener() {
                @Override
                public void onSuccess() {
                    // The connection may not yet be established.  We still need to wait
                    // for WIFI_P2P_CONNECTION_CHANGED_ACTION.  However, we might never
                    // get that broadcast, so we register a timeout.
                    Slog.i(TAG, "Initiated connection to Wifi display: " + newDevice.deviceName);

                    mHandler.postDelayed(mConnectionTimeout, CONNECTION_TIMEOUT_SECONDS * 1000);
                }

                @Override
                public void onFailure(int reason) {
                    if (mConnectingDevice == newDevice) {
                        Slog.i(TAG, "Failed to initiate connection to Wifi display: "
                                + newDevice.deviceName + ", reason=" + reason);
                        mConnectingDevice = null;
                        handleConnectionFailure(false);
                    }
                }
            });

            /// M: Modify for speed up rtsp setup @{
            if (true == mDRMContent_Mediaplayer) {
                setRemoteSubmixOn(false);
            } else {
                setRemoteSubmixOn(true);
            }
            
            final WifiP2pDevice oldDevice = mConnectingDevice;
            final int port = getPortNumber(mConnectingDevice);
            final String iface = "127.0.0.1" + ":" + port;
            mRemoteDisplayInterface = iface;

            mWifiP2pManager.setWfdSessionMode(mWifiP2pChannel, WifiP2pWfdInfo.SETUP, null);  ///Add by MTK
            Slog.i(TAG, "Listening for RTSP connection on " + iface
                    + " from Wifi display: " + mConnectingDevice.deviceName 
                    + " , Speed-Up rtsp setup, DRM Content isPlaying = " + mDRMContent_Mediaplayer);

            mRemoteDisplay = RemoteDisplay.listen(iface, new RemoteDisplay.Listener() {
                @Override
                public void onDisplayConnected(Surface surface,
                        int width, int height, int flags) {
                    /// M: rtsp connected callback faster than wifi broadcast @{
                    if (null != mConnectingDevice) {
                        mConnectedDevice = mConnectingDevice;
                    }
                    if (mConnectedDevice != oldDevice || mRemoteDisplayConnected) {
                        if (DEBUG) {
                            Slog.e(TAG, "!!RTSP connected condition GOT Trobule:" +
                                "\nmConnectedDevice: " + mConnectedDevice +
                                "\noldDevice: " + oldDevice + 
                                "\nmRemoteDisplayConnected: " + mRemoteDisplayConnected);
                        }
                    }
                    // M: ApusOne WifiP2pDevice will change some value(wpsConfigMethodsSupported, status) when connected!
                    if (null!=mConnectedDevice && null!=oldDevice &&
                        mConnectedDevice.deviceAddress.equals(oldDevice.deviceAddress) && 
                        !mRemoteDisplayConnected) {
                    //if (mConnectedDevice == oldDevice && !mRemoteDisplayConnected) {
                    ///@}
                        Slog.i(TAG, "Opened RTSP connection with Wifi display: "
                                + mConnectedDevice.deviceName);
                        mRemoteDisplayConnected = true;
                        mHandler.removeCallbacks(mRtspTimeout);
                        /// M: @{
                        mWifiP2pManager.setWfdSessionMode(mWifiP2pChannel, WifiP2pWfdInfo.PLAY, null);   ///Add by MTK

                        if (WFDCONTROLLER_QE_ON){
                            // For Quality Enhancement
                            mHandler.postDelayed(mWifiLinkInfo, WFDCONTROLLER_LINK_INFO_PERIOD_MILLIS);   ///Add by MTK
                            resetSignalParam();
                        }
                        ///@}   
                        updateWfdStatFile(WFDCONTROLLER_WFD_STAT_STREAMING);  ///Add by MTK
                        final WifiDisplay display = createWifiDisplay(mConnectedDevice);
                        advertiseDisplay(display, surface, width, height, flags);
                    }
                }

                @Override
                public void onDisplayDisconnected() {
                    if (mConnectedDevice == oldDevice) {
                        Slog.i(TAG, "Closed RTSP connection with Wifi display: "
                                + mConnectedDevice.deviceName);
                        mHandler.removeCallbacks(mRtspTimeout);
                        disconnect();
                        /// M: @{
                        mWifiP2pManager.setWfdSessionMode(mWifiP2pChannel, WifiP2pWfdInfo.DISCONNECTED, null);
                        mHandler.removeCallbacks(mWifiLinkInfo);

                        clearNotify();
                        ///@}                    
                    }
                }

                @Override
                public void onDisplayError(int error) {
                    if (mConnectedDevice == oldDevice) {
                        Slog.i(TAG, "Lost RTSP connection with Wifi display due to error "
                                + error + ": " + mConnectedDevice.deviceName);
                        mHandler.removeCallbacks(mRtspTimeout);
                        handleConnectionFailure(false);
                    }
                }
                
                @Override
                public void onDisplayKeyEvent(int keyCode, int flags){
                    Slog.d(TAG, "onDisplayKeyEvent: keyCode" + keyCode + " flags:" + flags );
                    sendKeyEvent(keyCode,flags);
                }

                @Override
                public void onDisplayTouchEvent(int x, int y, int flags){
                    Slog.d(TAG, "onDisplayTouchEvent: x:" + x + " y:" + y );
                    sendTap(x,y);
                }

                @Override
                public void onDisplayGenericMsgEvent(int event){
                    Slog.d(TAG, "onDisplayGenericMsgEvent: " + event);
                }
                
            }, mHandler);

            mHandler.postDelayed(mRtspTimeout, RTSP_TIMEOUT_SECONDS * 1000);
            ///@}
            return; // wait for asynchronous callback
        }

        // Step 6. Listen for incoming connections.
        if (mConnectedDevice != null && mRemoteDisplay == null) {
            Inet4Address addr = getInterfaceAddress(mConnectedDeviceGroupInfo);
            if (addr == null) {
                Slog.i(TAG, "Failed to get local interface address for communicating "
                        + "with Wifi display: " + mConnectedDevice.deviceName);
                handleConnectionFailure(false);
                return; // done
            }
            /// M: Modify for speed up rtsp setup @{
            /* move to Step 5.
            setRemoteSubmixOn(true);

            final WifiP2pDevice oldDevice = mConnectedDevice;
            final int port = getPortNumber(mConnectedDevice);
            final String iface = addr.getHostAddress() + ":" + port;
            mRemoteDisplayInterface = iface;

            Slog.i(TAG, "Listening for RTSP connection on " + iface
                    + " from Wifi display: " + mConnectedDevice.deviceName);

            mRemoteDisplay = RemoteDisplay.listen(iface, new RemoteDisplay.Listener() {
                @Override
                public void onDisplayConnected(Surface surface,
                        int width, int height, int flags) {
                    if (mConnectedDevice == oldDevice && !mRemoteDisplayConnected) {
                        Slog.i(TAG, "Opened RTSP connection with Wifi display: "
                                + mConnectedDevice.deviceName);
                        mRemoteDisplayConnected = true;
                        mHandler.removeCallbacks(mRtspTimeout);
                        updateWfdStatFile(WFDCONTROLLER_WFD_STAT_STREAMING);  ///Add by MTK
                        final WifiDisplay display = createWifiDisplay(mConnectedDevice);
                        advertiseDisplay(display, surface, width, height, flags);
                    }
                }

                @Override
                public void onDisplayDisconnected() {
                    if (mConnectedDevice == oldDevice) {
                        Slog.i(TAG, "Closed RTSP connection with Wifi display: "
                                + mConnectedDevice.deviceName);
                        mHandler.removeCallbacks(mRtspTimeout);
                        disconnect();
                    }
                }

                @Override
                public void onDisplayError(int error) {
                    if (mConnectedDevice == oldDevice) {
                        Slog.i(TAG, "Lost RTSP connection with Wifi display due to error "
                                + error + ": " + mConnectedDevice.deviceName);
                        mHandler.removeCallbacks(mRtspTimeout);
                        handleConnectionFailure(false);
                    }
                }
                ///M:@{
                @Override
                public void onDisplayKeyEvent(int keyCode, int flags){
                
                    Slog.d(TAG, "onDisplayKeyEvent: keyCode" + keyCode + " flags:" + flags );
                    sendKeyEvent(keyCode,flags);
                }

                @Override
                public void onDisplayTouchEvent(int x, int y, int flags){
                    Slog.d(TAG, "onDisplayTouchEvent: x:" + x + " y:" + y );                
                    sendTap(x,y);
                }

                @Override
                public void onDisplayGenericMsgEvent(int event){
                    Slog.d(TAG, "onDisplayGenericMsgEvent: " + event);
                    
                }                
                ///@}
            }, mHandler);

            mHandler.postDelayed(mRtspTimeout, RTSP_TIMEOUT_SECONDS * 1000);
            */
        }
    }

    private void setRemoteSubmixOn(boolean on) {
        if (mRemoteSubmixOn != on) {
            mRemoteSubmixOn = on;
            mAudioManager.setRemoteSubmixOn(on, REMOTE_SUBMIX_ADDRESS);
        }
    }

    private void handleStateChanged(boolean enabled) {
        mWifiP2pEnabled = enabled;
        updateWfdEnableState();
        /// M: ALPS00812236: dismiss all dialogs when wifi p2p is disabled @{
        if (false == enabled) {
            dismissDialog();
        }        
        ///@}
    }

    private void handlePeersChanged() {
        // Even if wfd is disabled, it is best to get the latest set of peers to
        // keep in sync with the p2p framework
        requestPeers();
    }

    /// M: reconnect when wifi p2p disconnect and reason is frequency conflict @{
    //private void handleConnectionChanged(NetworkInfo networkInfo) {
    private void handleConnectionChanged(NetworkInfo networkInfo, int reason) {
    ///@}
        mNetworkInfo = networkInfo;
        if (mWfdEnabled && networkInfo.isConnected()) {
            if (mDesiredDevice != null) {
                mWifiP2pManager.requestGroupInfo(mWifiP2pChannel, new GroupInfoListener() {
                    @Override
                    public void onGroupInfoAvailable(WifiP2pGroup info) {
                        if (DEBUG) {
                            Slog.d(TAG, "Received group info: " + describeWifiP2pGroup(info));
                        }

                        if (mConnectingDevice != null && !info.contains(mConnectingDevice)) {
                            Slog.i(TAG, "Aborting connection to Wifi display because "
                                    + "the current P2P group does not contain the device "
                                    + "we expected to find: " + mConnectingDevice.deviceName
                                    + ", group info was: " + describeWifiP2pGroup(info));
                            handleConnectionFailure(false);
                            return;
                        }

                        if (mDesiredDevice != null && !info.contains(mDesiredDevice)) {
                            Slog.i(TAG, "Aborting connection to Wifi display because "
                                + "the current P2P group does not contain the device "
                                + "we desired to find: " + mDesiredDevice.deviceName
                                + ", group info was: " + describeWifiP2pGroup(info));
                            disconnect();
                            return;
                        }

                        if (mConnectingDevice != null && mConnectingDevice == mDesiredDevice) {
                            Slog.i(TAG, "Connected to Wifi display: "
                                    + mConnectingDevice.deviceName);

                            mHandler.removeCallbacks(mConnectionTimeout);
                            mConnectedDeviceGroupInfo = info;
                            mConnectedDevice = mConnectingDevice;
                            mConnectingDevice = null;
                            updateWfdStatFile(WFDCONTROLLER_WFD_STAT_STANDBY);  ///Add by MTK
                            updateConnection();
                        }
                    }
                });
            }
        } else {
            disconnect();

            // After disconnection for a group, for some reason we have a tendency
            // to get a peer change notification with an empty list of peers.
            // Perform a fresh scan.
            if (mWfdEnabled) {
                requestPeers();
            }
            
            /// M: frequency conflict is NO_COMMON_CHANNEL==7  @{
            if (7==reason && null!=mReConnectDevice) {
                Slog.i(TAG, "reconnect procedure start, ReConnectDevice = " + mReConnectDevice);
                dialogReconnect();
            }
            ///@}
        }

        ///M: other Wifi P2p trigger connection @{
        if (null == mDesiredDevice) {
            mIsConnected_OtherP2p = networkInfo.isConnected();
            if (true == mIsConnected_OtherP2p) {
                Slog.w(TAG, "Wifi P2p connection is connected but it does not wifidisplay trigger");
                resetReconnectVariable();
            }
        }
        ///@}
    }

    private final Runnable mConnectionTimeout = new Runnable() {
        @Override
        public void run() {
            if (mConnectingDevice != null && mConnectingDevice == mDesiredDevice) {
                Slog.i(TAG, "Timed out waiting for Wifi display connection after "
                        + CONNECTION_TIMEOUT_SECONDS + " seconds: "
                        + mConnectingDevice.deviceName);
                handleConnectionFailure(true);
            }
        }
    };

    private final Runnable mRtspTimeout = new Runnable() {
        @Override
        public void run() {
            if (mConnectedDevice != null
                    && mRemoteDisplay != null && !mRemoteDisplayConnected) {
                Slog.i(TAG, "Timed out waiting for Wifi display RTSP connection after "
                        + RTSP_TIMEOUT_SECONDS + " seconds: "
                        + mConnectedDevice.deviceName);
                handleConnectionFailure(true);
            }
        }
    };

    private void handleConnectionFailure(boolean timeoutOccurred) {
        Slog.i(TAG, "Wifi display connection failed!");

        if (mDesiredDevice != null) {
            if (mConnectionRetriesLeft > 0) {
                final WifiP2pDevice oldDevice = mDesiredDevice;
                mHandler.postDelayed(new Runnable() {
                    @Override
                    public void run() {
                        if (mDesiredDevice == oldDevice && mConnectionRetriesLeft > 0) {
                            mConnectionRetriesLeft -= 1;
                            Slog.i(TAG, "Retrying Wifi display connection.  Retries left: "
                                    + mConnectionRetriesLeft);
                            retryConnection();
                        }
                    }
                }, timeoutOccurred ? 0 : CONNECT_RETRY_DELAY_MILLIS);
            } else {
                disconnect();
            }
        }
    }

    private void advertiseDisplay(final WifiDisplay display,
            final Surface surface, final int width, final int height, final int flags) {
        if (DEBUG) {
            Slog.d(TAG, "advertiseDisplay(): ----->" 
                + "\n\tdisplay: " + display
                + "\n\tsurface: " + surface
                + "\n\twidth: " + width
                + "\n\theight: " + height
                + "\n\tflags: " + flags
                );
        }
        if (!Objects.equal(mAdvertisedDisplay, display)
                || mAdvertisedDisplaySurface != surface
                || mAdvertisedDisplayWidth != width
                || mAdvertisedDisplayHeight != height
                || mAdvertisedDisplayFlags != flags
                ) {   ///Added by MTK
            final WifiDisplay oldDisplay = mAdvertisedDisplay;
            final Surface oldSurface = mAdvertisedDisplaySurface;

            mAdvertisedDisplay = display;
            mAdvertisedDisplaySurface = surface;
            mAdvertisedDisplayWidth = width;
            mAdvertisedDisplayHeight = height;
            mAdvertisedDisplayFlags = flags;

            mHandler.post(new Runnable() {
                @Override
                public void run() {
                    if (DEBUG) {
                        Slog.d(TAG, "oldSurface = " + oldSurface + ", surface = " + surface +
                            ", oldDisplay = " + oldDisplay + ", display = " + display);
                    }
                  
                    if (oldSurface != null && surface != oldSurface) {
                        Slog.d(TAG, "callback onDisplayDisconnected()");
                        mListener.onDisplayDisconnected();
                        actionAtDisconnected(oldDisplay);  ///Add by MTK
                    } else if (oldDisplay != null && !oldDisplay.hasSameAddress(display)) {
                        Slog.d(TAG, "callback onDisplayConnectionFailed()");
                        mListener.onDisplayConnectionFailed();
                        actionAtConnectionFailed();  ///Add by MTK
                    }

                    if (display != null) {
                        if (!display.hasSameAddress(oldDisplay)) {
                            Slog.d(TAG, "callback onDisplayConnecting(): display = " + display);
                            mListener.onDisplayConnecting(display);
                            actionAtConnecting();  ///Add by MTK
                        } else if (!display.equals(oldDisplay)) {
                            // The address is the same but some other property such as the
                            // name must have changed.
                            mListener.onDisplayChanged(display);
                        }
                        if (surface != null && surface != oldSurface) {
                            Slog.d(TAG, "callback onDisplayConnected()"
                                + ": display = " + display
                                + ", surface = " + surface
                                + ", width = " + width 
                                + ", height = " + height
                                + ", flags = " + flags);
                            mListener.onDisplayConnected(display, surface, width, height, flags);
                            actionAtConnected(display);  ///Add by MTK
                        }
                    }
                }
            });
        }
        ///M:@{
        else {
            if (DEBUG) {
                Slog.d(TAG, "advertiseDisplay() : no need update!");
            }
        }
        ///@}
    }

    private void unadvertiseDisplay() {
        advertiseDisplay(null, null, 0, 0, 0);
    }

    private void readvertiseDisplay(WifiDisplay display) {
        advertiseDisplay(display, mAdvertisedDisplaySurface,
                mAdvertisedDisplayWidth, mAdvertisedDisplayHeight,
                mAdvertisedDisplayFlags);
    }

    private static Inet4Address getInterfaceAddress(WifiP2pGroup info) {
        NetworkInterface iface;
        try {
            iface = NetworkInterface.getByName(info.getInterface());
        } catch (SocketException ex) {
            Slog.w(TAG, "Could not obtain address of network interface "
                    + info.getInterface(), ex);
            return null;
        }

        Enumeration<InetAddress> addrs = iface.getInetAddresses();
        while (addrs.hasMoreElements()) {
            InetAddress addr = addrs.nextElement();
            if (addr instanceof Inet4Address) {
                return (Inet4Address)addr;
            }
        }

        Slog.w(TAG, "Could not obtain address of network interface "
                + info.getInterface() + " because it had no IPv4 addresses.");
        return null;
    }

    private static int getPortNumber(WifiP2pDevice device) {
        if (device.deviceName.startsWith("DIRECT-")
                && device.deviceName.endsWith("Broadcom")) {
            // These dongles ignore the port we broadcast in our WFD IE.
            return 8554;
        }
        return DEFAULT_CONTROL_PORT;
    }

    private static boolean isWifiDisplay(WifiP2pDevice device) {
        return device.wfdInfo != null
                && device.wfdInfo.isWfdEnabled()
                && device.wfdInfo.isSessionAvailable()  ///Add by MTK
                && isPrimarySinkDeviceType(device.wfdInfo.getDeviceType());
    }

    private static boolean isPrimarySinkDeviceType(int deviceType) {
        return deviceType == WifiP2pWfdInfo.PRIMARY_SINK
                || deviceType == WifiP2pWfdInfo.SOURCE_OR_PRIMARY_SINK;
    }

    private static String describeWifiP2pDevice(WifiP2pDevice device) {
        return device != null ? device.toString().replace('\n', ',') : "null";
    }

    private static String describeWifiP2pGroup(WifiP2pGroup group) {
        return group != null ? group.toString().replace('\n', ',') : "null";
    }

    private static WifiDisplay createWifiDisplay(WifiP2pDevice device) {
        return new WifiDisplay(device.deviceAddress, device.deviceName, null);
    }

    private final BroadcastReceiver mWifiP2pReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            final String action = intent.getAction();
            if (action.equals(WifiP2pManager.WIFI_P2P_STATE_CHANGED_ACTION)) {
                // This broadcast is sticky so we'll always get the initial Wifi P2P state
                // on startup.
                boolean enabled = (intent.getIntExtra(WifiP2pManager.EXTRA_WIFI_STATE,
                        WifiP2pManager.WIFI_P2P_STATE_DISABLED)) ==
                        WifiP2pManager.WIFI_P2P_STATE_ENABLED;
                if (DEBUG) {
                    Slog.d(TAG, "Received WIFI_P2P_STATE_CHANGED_ACTION: enabled="
                            + enabled);
                }

                handleStateChanged(enabled);
            } else if (action.equals(WifiP2pManager.WIFI_P2P_PEERS_CHANGED_ACTION)) {
                if (DEBUG) {
                    Slog.d(TAG, "Received WIFI_P2P_PEERS_CHANGED_ACTION.");
                }

                handlePeersChanged();
            } else if (action.equals(WifiP2pManager.WIFI_P2P_CONNECTION_CHANGED_ACTION)) {
                NetworkInfo networkInfo = (NetworkInfo)intent.getParcelableExtra(
                        WifiP2pManager.EXTRA_NETWORK_INFO);
                ///M: ALPS00677009: receive p2p broadcast to know the group removed reason @{
                int reason = intent.getIntExtra("reason=", -1);
                if (DEBUG) {
                    Slog.d(TAG, "Received WIFI_P2P_CONNECTION_CHANGED_ACTION: networkInfo="
                        + networkInfo + ", reason = " + reason);
                } else {
                    Slog.d(TAG, "Received WIFI_P2P_CONNECTION_CHANGED_ACTION: isConnected? "
                        + networkInfo.isConnected() + ", reason = " + reason);
                }

                //handleConnectionChanged(networkInfo);
                handleConnectionChanged(networkInfo, reason);
                ///@}
            }
            ///M:@{
            else if (action.equals(DRM_CONTENT_MEDIAPLAYER)) {
                int playerID = 0;
                mDRMContent_Mediaplayer = intent.getBooleanExtra("isPlaying", false);
                playerID = intent.getIntExtra("playerId", 0);
                Slog.i(TAG, "Received DRM_CONTENT_MEDIAPLAYER: isPlaying = " + mDRMContent_Mediaplayer
                        + ", player = " + playerID
                        + ", isConnected = " + mIsWFDConnected);

                if (true == mIsWFDConnected) {
                    if (true == mDRMContent_Mediaplayer) {
                        setRemoteSubmixOn(false);
                        mPlayerID_Mediaplayer = playerID;
                    } else {
                        if (mPlayerID_Mediaplayer == playerID) {
                            setRemoteSubmixOn(true);
                        } else {
                            Slog.w(TAG, "player ID doesn't match last time: " + mPlayerID_Mediaplayer);
                        }
                    }
                }
            }
            /*M: ALPS00645645: add protection if scan result isn't replied from supplicant*/
            else if (action.equals(WifiP2pManager.WIFI_P2P_DISCOVERY_CHANGED_ACTION)) {
                int discoveryState = intent.getIntExtra(WifiP2pManager.EXTRA_DISCOVERY_STATE,
                    WifiP2pManager.WIFI_P2P_DISCOVERY_STOPPED);
                if (DEBUG) {
                    Slog.d(TAG, "Received WIFI_P2P_DISCOVERY_CHANGED_ACTION: discoveryState="
                        + discoveryState);
                }
                if (discoveryState == WifiP2pManager.WIFI_P2P_DISCOVERY_STOPPED) {
                    handleScanFinished();
                }
            }
            /*M: ALPS00716611: BT/WFD exclude completely*/
            else if (action.equals(BluetoothAdapter.ACTION_STATE_CHANGED)) {
                int stateBT = intent.getIntExtra(BluetoothAdapter.EXTRA_STATE, BluetoothAdapter.ERROR);
                switch (stateBT) {
                    case BluetoothAdapter.STATE_OFF:
                        mBTOnSetting = false;
                        break;
                    default:
                        mBTOnSetting = true;
                        break;
                }
                if (DEBUG) {
                    Slog.d(TAG, "Received BluetoothAdapter.ACTION_STATE_CHANGED: mBTOnSetting =" + mBTOnSetting
                        + ", stateBT = " + stateBT);
                }
            }
            /*M: ALPS00772074: do disconnect for every power-off case*/
            else if (action.equals(WFDCONTROLLER_PRE_SHUTDOWN)) {
                Slog.i(TAG, "Received " + WFDCONTROLLER_PRE_SHUTDOWN
                    + ", do disconnect anyway");

                // non-blocking API first
                if (null != mWifiP2pManager) {
                    mWifiP2pManager.removeGroup(mWifiP2pChannel, null);
                }
                // blocking API after
                if (null != mRemoteDisplay) {
                    mRemoteDisplay.dispose();
                }
            }
            ///@}
        }
    };

    /**
     * Called on the handler thread when displays are connected or disconnected.
     */
    public interface Listener {
        void onFeatureStateChanged(int featureState);

        void onScanStarted();
        void onScanFinished(WifiDisplay[] availableDisplays);

        void onDisplayConnecting(WifiDisplay display);
        void onDisplayConnectionFailed();
        void onDisplayChanged(WifiDisplay display);
        void onDisplayConnected(WifiDisplay display,
                Surface surface, int width, int height, int flags);
        void onDisplayDisconnected();
        void onDisplayDisconnecting();  ///Add by MTK
    }
    
    ///Add by MTK @{
    private void sendKeyEvent(int keyCode, int isDown) {
        long now = SystemClock.uptimeMillis();
        if(isDown==1){
            injectKeyEvent(new KeyEvent(now, now, KeyEvent.ACTION_DOWN, translateAsciiToKeyCode(keyCode), 0, 0,
            KeyCharacterMap.VIRTUAL_KEYBOARD, 0, 0, InputDevice.SOURCE_KEYBOARD));
        }else{
            injectKeyEvent(new KeyEvent(now, now, KeyEvent.ACTION_UP, translateAsciiToKeyCode(keyCode), 0, 0,
            KeyCharacterMap.VIRTUAL_KEYBOARD, 0, 0, InputDevice.SOURCE_KEYBOARD));
        }            
    }

    private void sendTap(float x, float y) {
        long now = SystemClock.uptimeMillis();
        injectPointerEvent(MotionEvent.obtain(now, now, MotionEvent.ACTION_DOWN, x, y, 0));
        injectPointerEvent(MotionEvent.obtain(now, now, MotionEvent.ACTION_UP, x, y, 0));
    }

    private void injectKeyEvent(KeyEvent event) {
        Slog.d(TAG, "InjectKeyEvent: " + event);
        InputManager.getInstance().injectInputEvent(event,
            InputManager.INJECT_INPUT_EVENT_MODE_WAIT_FOR_FINISH);
    }

    private void injectPointerEvent(MotionEvent event) {
        event.setSource(InputDevice.SOURCE_TOUCHSCREEN);
        Slog.d("Input", "InjectPointerEvent: " + event);
        InputManager.getInstance().injectInputEvent(event,
            InputManager.INJECT_INPUT_EVENT_MODE_WAIT_FOR_FINISH);
    }

    //Support for UIBC mechanism
    private int translateSpecialCode(int ascii){
        int newKeyCode = 0;
        switch(ascii){
        case 8: //Backspace
            newKeyCode = KeyEvent.KEYCODE_DEL;
          break;
        case 13:
            newKeyCode = KeyEvent.KEYCODE_ENTER;
            break;
        case 16:
            newKeyCode = KeyEvent.KEYCODE_SHIFT_LEFT;
            break;
        case 20:
            newKeyCode = KeyEvent.KEYCODE_CAPS_LOCK;
            break;
        case 32: //space
            newKeyCode = KeyEvent.KEYCODE_SPACE;
            break;
        case 12: //Enter
            newKeyCode = KeyEvent.KEYCODE_ENTER;
            break;
        case 190: //.
            newKeyCode = KeyEvent.KEYCODE_PERIOD;
            break;
        case 188: //,
            newKeyCode = KeyEvent.KEYCODE_COMMA;
            break;
        case 191:  //'/'
            newKeyCode = KeyEvent.KEYCODE_SLASH;
            break;
        case 220: //'\'
            newKeyCode = KeyEvent.KEYCODE_BACKSLASH;
            break;
        case 34: //page down
            newKeyCode = KeyEvent.KEYCODE_PAGE_UP;
            break;
        case 33: //page up
            newKeyCode = KeyEvent.KEYCODE_PAGE_DOWN;
            break;
        case 37: // up
            newKeyCode = KeyEvent.KEYCODE_DPAD_UP;
            break;
        case 38: //down
            newKeyCode = KeyEvent.KEYCODE_DPAD_DOWN;
            break;
        case 39: //Right
            newKeyCode = KeyEvent.KEYCODE_DPAD_RIGHT;
            break;
        case 40: //Left
            newKeyCode = KeyEvent.KEYCODE_DPAD_LEFT;
            break;
        case 27: //Esc
            newKeyCode = KeyEvent.KEYCODE_ESCAPE;
            break;
        case 219: //[
            newKeyCode = KeyEvent.KEYCODE_LEFT_BRACKET;
            break; 
        case 221: //]
            newKeyCode = KeyEvent.KEYCODE_RIGHT_BRACKET;
            break;
        case 192:
            newKeyCode = KeyEvent.KEYCODE_GRAVE;
            break;                
        case 189:
            newKeyCode = KeyEvent.KEYCODE_MINUS;
            break;
        case 187:
            newKeyCode = KeyEvent.KEYCODE_EQUALS;
            break;
        case 186:
            newKeyCode = KeyEvent.KEYCODE_SEMICOLON;
            break;
        case 222:
            newKeyCode = KeyEvent.KEYCODE_APOSTROPHE;
            break;
        }

        return newKeyCode;
    }

    private  int translateAsciiToKeyCode(int ascii){
        if(ascii>=48 && ascii <=57){  // 0~9
            return (ascii-41);
        }else if(ascii >=65 && ascii <=90){//A~Z
            return (ascii-36);
        }else{
            int newKeyCode = translateSpecialCode(ascii);
            if(newKeyCode > 0){
                Slog.d(TAG, "special code: " + ascii + ":" + newKeyCode);
                return newKeyCode;
            }
            Slog.d(TAG, "translateAsciiToKeyCode: ascii is not supported" + ascii);
        }
        return 0;
    }
    
    private void getWifiLock() {
        if (null == mWifiManager) {
            mWifiManager = (WifiManager)mContext.getSystemService(Context.WIFI_SERVICE);
        }
        if (null==mWifiLock && null!=mWifiManager) {
            mWifiLock = mWifiManager.createWifiLock(WifiManager.WIFI_MODE_FULL , "WFD_WifiLock");    
        }
    }
    
    private void actionAtConnected(WifiDisplay display) {
        /* Keep Google MR1 original behavior
        if (DEBUG) {
            Slog.d(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() + ", mIsNeedRotate = " + mIsNeedRotate);
        }
        if (true == mIsNeedRotate) {
            Settings.System.putInt(mContext.getContentResolver(), Settings.System.USER_ROTATION, Surface.ROTATION_90);
        }
        mBackupShowTouchVal = Settings.System.getInt(mContext.getContentResolver(), Settings.System.SHOW_TOUCHES, 0);
        Settings.System.putInt(mContext.getContentResolver(), Settings.System.SHOW_TOUCHES, 1);
        Settings.System.putInt(mContext.getContentResolver(), Settings.System.ACCELEROMETER_ROTATION, WindowManagerPolicy.USER_ROTATION_FREE);
        //mBackupScreenOffTimeout = Settings.System.getInt(mContext.getContentResolver(), Settings.System.SCREEN_OFF_TIMEOUT, 0); 
        //Settings.System.putInt(mContext.getContentResolver(), Settings.System.SCREEN_OFF_TIMEOUT, 30*60*1000);  // 30minutes
        */
        mIsWFDConnected = true;
        
        Intent intent = new Intent(WFD_CONNECTION);
        intent.addFlags(Intent.FLAG_RECEIVER_REGISTERED_ONLY_BEFORE_BOOT);
        intent.putExtra("connected", 1);
        if (null != display) {
            intent.putExtra("device_address", display.getDeviceAddress());
            intent.putExtra("device_name", display.getDeviceName());
            intent.putExtra("device_alias", display.getDeviceAlias());
        } else {
            Slog.e(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() + ", null display");
            intent.putExtra("device_address", "00:00:00:00:00:00");
            intent.putExtra("device_name", "wifidisplay dongle");
            intent.putExtra("device_alias", "wifidisplay dongle");
        }
        try {
            mContext.sendStickyBroadcastAsUser(intent, UserHandle.ALL);
        } catch (Exception e) {
            Slog.e(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() 
                + ", failed to sendStickyBroadcastAsUser(): " + e);
        }

        if (true == mReConnecting) {
            resetReconnectVariable();
        } 

        getWifiLock();
        if (null!=mWifiManager && null!=mWifiLock) {
            if(!mWifiLock.isHeld()){
                if (DEBUG) {
                    Slog.i(TAG, "acquire wifilock");
                }
                mWifiLock.acquire();
            } else {
                Slog.e(TAG, "WFD connected, and WifiLock is Held!");
            }
        } else {
            Slog.e(TAG, "actionAtConnected(): mWifiManager: " + mWifiManager
                + ", mWifiLock: " + mWifiLock);
        }

    }

    private void actionAtDisconnected(WifiDisplay display) {
        /* Keep Google MR1 original behavior
        if (DEBUG) {
            Slog.d(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() + ", mIsNeedRotate = " + mIsNeedRotate);
        }
        if (true == mIsNeedRotate) {
            Settings.System.putInt(mContext.getContentResolver(), Settings.System.USER_ROTATION, Surface.ROTATION_0);
        }
        Settings.System.putInt(mContext.getContentResolver(), Settings.System.SHOW_TOUCHES, mBackupShowTouchVal);
        Settings.System.putInt(mContext.getContentResolver(), Settings.System.ACCELEROMETER_ROTATION, WindowManagerPolicy.USER_ROTATION_LOCKED);
        //Settings.System.putInt(mContext.getContentResolver(), Settings.System.SCREEN_OFF_TIMEOUT, mBackupScreenOffTimeout);
        */
        mIsWFDConnected = false;

        Intent intent = new Intent(WFD_CONNECTION);
        intent.addFlags(Intent.FLAG_RECEIVER_REGISTERED_ONLY_BEFORE_BOOT);
        intent.putExtra("connected", 0);
        if (null != display) {
            intent.putExtra("device_address", display.getDeviceAddress());
            intent.putExtra("device_name", display.getDeviceName());
            intent.putExtra("device_alias", display.getDeviceAlias());
        } else {
            Slog.e(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() + ", null display");
            intent.putExtra("device_address", "00:00:00:00:00:00");
            intent.putExtra("device_name", "wifidisplay dongle");
            intent.putExtra("device_alias", "wifidisplay dongle");
        }
        try {
            mContext.sendStickyBroadcastAsUser(intent, UserHandle.ALL);
        } catch (Exception e) {
            Slog.e(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() 
                + ", failed to sendStickyBroadcastAsUser(): " + e);
        }

        if (true == mReConnecting) {
            Toast.makeText(mContext, com.mediatek.internal.R.string.wifi_display_disconnected
                , Toast.LENGTH_SHORT).show();
            resetReconnectVariable();
        }        

        getWifiLock();
        if (null!=mWifiManager && null!=mWifiLock) {
            if (mWifiLock.isHeld()) {
                if (DEBUG) {
                    Slog.i(TAG, "release wifilock");
                }
                mWifiLock.release();
            } else {
                Slog.e(TAG, "WFD disconnected, and WifiLock isn't Held!");
            }
        } else {
            Slog.e(TAG, "actionAtDisconnected(): mWifiManager: " + mWifiManager
                + ", mWifiLock: " + mWifiLock);
        }

    }

    private void actionAtConnecting() {
        if (null != mReConnectDevice) {
            mReConnecting = true;
        }
    }

    private void actionAtConnectionFailed() {
        if (true == mReConnecting) {
            Toast.makeText(mContext, com.mediatek.internal.R.string.wifi_display_disconnected
                , Toast.LENGTH_SHORT).show();
            resetReconnectVariable();
        }
    }

    private int loadWfdWpsSetup() {
        String wfdWpsSetup = SystemProperties.get("wlan.wfd.wps.setup", "1");
        if (DEBUG) {
            Slog.d(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() + ", wfdWpsSetup = " + wfdWpsSetup);
        }
        switch (Integer.valueOf(wfdWpsSetup)) {
            case 0:
                return WpsInfo.KEYPAD;
            case 1:
                return WpsInfo.PBC;
            default:
                return WpsInfo.PBC;
        }
    }

    private void loadDebugLevel() {
        String debugLevel = SystemProperties.get("wlan.wfd.controller.debug", "0");
        if (DEBUG) {
            Slog.d(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() + ", debugLevel = " + debugLevel);
        }
        switch (Integer.valueOf(debugLevel)) {
            case 0:
                DEBUG = false;
                break;
            case 1:
                DEBUG = true;
                break;
            default:
                DEBUG = false;
                break;
        }
    }

    private void updateSettingsHDMI() {
        final ContentResolver resolver = mContext.getContentResolver();
        mHDMIOnSetting = Settings.System.getInt(resolver,
                WFDCONTROLLER_HDMI_ENABLE_CONFIG, 0) != 0;

        if (true==mHDMIOnSetting && true==mWifiDisplayOnSetting) {
            if (WifiDisplayStatus.FEATURE_STATE_ON == computeFeatureState()) {
                dialogWfdHdmiConflict(WFDCONTROLLER_HDMI_UPDATE);

            } else {
                if (DEBUG) {
                    Slog.d(TAG, "HDMI on and WFD feature state isn't on --> turn off WifiDisplay directly");
                }
                Settings.Global.putInt(mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_ON, 0);
            }
            
        }
    }

    private void updateWfdStatFile(int wfd_stat) {
        /* disable it due to native module is not ready
        if (DEBUG) {
            Slog.d(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() + ", wfd_stat = " + wfd_stat);
        }

        try {
            FileOutputStream fbp = new FileOutputStream(WFDCONTROLLER_WFD_STAT_FILE);
            fbp.write(wfd_stat);
            fbp.flush();
            fbp.close();
        } catch (FileNotFoundException e) {
            if (DEBUG) {
                Slog.e(TAG, "Failed to find " + WFDCONTROLLER_WFD_STAT_FILE);
            }
        } catch (java.io.IOException e) {
            if (DEBUG) {
                Slog.e(TAG, "Failed to open " + WFDCONTROLLER_WFD_STAT_FILE);
            }
        }
        */
    }

    private void dialogWfdBtConflict(int which) {
        if (DEBUG) {
            Slog.d(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() 
                + ", which = " + which );
        }
        if (null == mBTAdapter) {
            mBTAdapter = BluetoothAdapter.getDefaultAdapter();
        }
        if (null == mHdmiNative) {
            mHdmiNative = MediatekClassFactory.createInstance(IHDMINative.class);
        }

        if (WFDCONTROLLER_WFD_UPDATE == which) {
            if (DEBUG) {
                Slog.i(TAG, "WifiDisplay is ON and going to popup dialog -> turn off WifiDisplay functionality first!");
            }

            mWifiDisplayOnSetting = false;
            updateWfdEnableState();
            showDialog(WFD_BT_EXCLUDED_DIALOG);
        } 

    }

    private void dialogWfdHdmiConflict(int which) {
        if (DEBUG) {
            Slog.d(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() 
                + ", which = " + which );
        }
        if (null == mHdmiNative) {
            mHdmiNative = MediatekClassFactory.createInstance(IHDMINative.class);
        }
        if (null == mBTAdapter) {
            mBTAdapter = BluetoothAdapter.getDefaultAdapter();
        }

        if (WFDCONTROLLER_WFD_UPDATE == which) {
            showDialog(WFD_HDMI_EXCLUDED_DIALOG_WFD_UPDATE);

        } else if (WFDCONTROLLER_HDMI_UPDATE == which) {
            showDialog(WFD_HDMI_EXCLUDED_DIALOG_HDMI_UPDATE);

        }

    }

    private static final Pattern wfdLinkInfoPattern = Pattern.compile(
            "sta_addr=((?:[0-9a-f]{2}:){5}[0-9a-f]{2}|any)\n" +
            "link_score=(.*)\n" + 
            "per=(.*)\n" + 
            "rssi=(.*)\n" +
            "phy=(.*)\n" + 
            "rate=(.*)\n" + 
            "total_cnt=(.*)\n" + 
            "threshold_cnt=(.*)\n" + 
            "fail_cnt=(.*)\n" + 
            "timeout_cnt=(.*)\n" + 
            "apt=(.*)\n" + 
            "aat=(.*)\n" + 
            "TC_buf_full_cnt=(.*)\n" + 
            "TC_sta_que_len=(.*)\n" + 
            "TC_avg_que_len=(.*)\n" + 
            "TC_cur_que_len=(.*)\n" + 
            "flag=(.*)\n" + 
            "reserved0=(.*)\n" + 
            "reserved1=(.*)" );

    private final Runnable mWifiLinkInfo = new Runnable() {
        @Override
        public void run() {
            if (null == mConnectedDevice) {
                Slog.e(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() + ": ConnectedDevice is null");

            } else if (null == mRemoteDisplay) {
                Slog.e(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() + ": RemoteDisplay is null");

            } else {
                mWifiP2pManager.requestWfdLinkInfo(mWifiP2pChannel, mConnectedDevice.deviceAddress, new WfdLinkInfoListener() {
                    @Override
                    public void onLinkInfoAvailable(WfdLinkInfo status) {
                        //if (DEBUG) {
                        //    Slog.i(TAG, Thread.currentThread().getStackTrace()[2].getMethodName() + ", linkInfo: \n" + status.linkInfo);
                        //}

                        if (null!=status && null!=status.linkInfo) {
                            Matcher match;
                            match = wfdLinkInfoPattern.matcher(status.linkInfo);
                            if (match.find()) {
                                int score = parseDec(match.group(2));
                                int rssi = parseDec(match.group(4));                           

                                // Update signal level
                                updateSignalLevel(score, rssi);                           

                            } else {
                                Slog.e(TAG, "wfdLinkInfoPattern Malformed Pattern, not match String ");

                            }

                        } else {
                            Slog.e(TAG, "onLinkInfoAvailable() parameter is null!");

                        }

                    }

                });               

                mHandler.postDelayed(mWifiLinkInfo, WFDCONTROLLER_LINK_INFO_PERIOD_MILLIS);
            }

        }
    };

    private int parseDec(String decString) {
        int num = 0;

        try {
            num = Integer.parseInt(decString);
        } catch (NumberFormatException e) {
            Slog.e(TAG,"Failed to parse dec string " + decString);
        }
        return num;
    }    

    
    private void updateSignalLevel(int score, int rssi){

        // Update average score
        int avarageScore = getAverageScore(score);

        // Update score level
        updateScoreLevel(avarageScore);        

        String message = "W:" + avarageScore +
                         //",rs:" + rssi + 
                         //",S:" + mScoreLevel +                        
                         ",L:" + mLevel;
                         
        // Update signal level
        if (mScoreLevel >= 6){
            
            //Set level to encoder
            if (mRemoteDisplay != null){
                if (DEBUG) {
                    Slog.d(TAG, "setWfdLevel():+2");
                }
                
                mRemoteDisplay.setWfdLevel(2);
                mLevel += 2;
            }             

            mScoreLevel = 0;
        }
        else if (mScoreLevel >= 4){
              
            //Set level to encoder
            if (mRemoteDisplay != null){
                if (DEBUG) {
                    Slog.d(TAG, "setWfdLevel():+1");
                } 
                mRemoteDisplay.setWfdLevel(1);
                mLevel += 1;
            }

            mScoreLevel = 0;

        }
        else if (mScoreLevel <= -6){            

            //Set level to encoder
            if (mRemoteDisplay != null){
                if (DEBUG) {
                    Slog.d(TAG, "setWfdLevel():-2");
                }
                mRemoteDisplay.setWfdLevel(-2);
                mLevel -= 2;
            }
            mScoreLevel = 0;
        }
        else if (mScoreLevel <= -4){

            //Set level to encoder
            if (mRemoteDisplay != null){
                if (DEBUG) {
                    Slog.d(TAG, "setWfdLevel():-1");
                }
                mRemoteDisplay.setWfdLevel(-1);
                mLevel -= 1;
            }
            mScoreLevel = 0;
        }

        // for log
        if (mLevel > 0)
            mLevel = 0;
        if (mLevel < -5)
            mLevel = -5;
        
        message += ">" + mLevel;

        // Handle level change
        handleLevelChange();
        
        if (null != mRemoteDisplay) {
            int expectedBitRate = mRemoteDisplay.getWfdParam(0);
            int currentBitRate = mRemoteDisplay.getWfdParam(1);
            int fluencyRate = mRemoteDisplay.getWfdParam(2);

            message += ",ER:" + expectedBitRate; 
            message += ",CR:" + currentBitRate; 

            if (fluencyRate != WFDCONTROLLER_INVALID_VALUE){            
                message += ",FR:" + fluencyRate;
            }

            if (WFDCONTROLLER_SQC_INFO_ON) {
                Toast.makeText(mContext, message, Toast.LENGTH_SHORT).show(); 
            }

            // print log
            //if (DEBUG) {
            Slog.d(TAG, message);
            //} 
            
        } else {
            Slog.e(TAG, "mRemoteDisplay is null");

        }
            
    }    

    private int getAverageScore(int score){

        mScore[mScoreIndex % WFDCONTROLLER_AVERATE_SCORE_COUNT] = score;
        mScoreIndex ++;

        int count = 0;
        int sum = 0;
        for (int i = 0; i < WFDCONTROLLER_AVERATE_SCORE_COUNT; i++){
            if (mScore[i] != WFDCONTROLLER_INVALID_VALUE){
                sum += mScore[i];
                count ++;
            }           
        }
        return sum / count;
    }
    private void updateScoreLevel(int score){
        if (score >= WFDCONTROLLER_SCORE_THRESHOLD1){
            if (mScoreLevel < 0){
                mScoreLevel = 0;
            }
            mScoreLevel += 6;
        }
        else if (score >= WFDCONTROLLER_SCORE_THRESHOLD2){
            if (mScoreLevel < 0){
                mScoreLevel = 0;
            }
            mScoreLevel += 2;
        }
        else if (score >= WFDCONTROLLER_SCORE_THRESHOLD3){
            if (mScoreLevel > 0){
                mScoreLevel = 0;
            }
            mScoreLevel -= 2;
        }
        else if (score >= WFDCONTROLLER_SCORE_THRESHOLD4){
            if (mScoreLevel > 0){
                mScoreLevel = 0;
            }
            mScoreLevel -= 3;
        }
        else{
            if (mScoreLevel > 0){
                mScoreLevel = 0;
            }
            mScoreLevel -= 6;
        }
    }

    private void resetSignalParam(){
        mLevel = 0;
        mScoreLevel = 0;

        mScoreIndex = 0;
        for (int i = 0; i < WFDCONTROLLER_AVERATE_SCORE_COUNT; i++){
            mScore[i] = WFDCONTROLLER_INVALID_VALUE;
        }

        mNotiTimerStarted = false;
        mToastTimerStarted = false;
        
    }

    private void registerEMObserver(){

        // Init parameter
        WFDCONTROLLER_DISPLAY_TOAST_TIME = mContext.getResources().getInteger(com.mediatek.internal.R.integer.wfd_display_toast_time);  
        WFDCONTROLLER_DISPLAY_NOTIFICATION_TIME = mContext.getResources().getInteger(com.mediatek.internal.R.integer.wfd_display_notification_time);  

        Slog.d(TAG, "registerEMObserver(), toast_time:" + WFDCONTROLLER_DISPLAY_TOAST_TIME +
                                           "notify_time:" + WFDCONTROLLER_DISPLAY_NOTIFICATION_TIME);
        
        // Init parameter
        Settings.Global.putInt(
            mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_DISPLAY_TOAST_TIME, WFDCONTROLLER_DISPLAY_TOAST_TIME);
        Settings.Global.putInt(
            mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_DISPLAY_NOTIFICATION_TIME, WFDCONTROLLER_DISPLAY_NOTIFICATION_TIME);
        Settings.Global.putInt(
            mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_SQC_INFO_ON, WFDCONTROLLER_SQC_INFO_ON ? 1 : 0);
        Settings.Global.putInt(
            mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_QE_ON, WFDCONTROLLER_QE_ON ? 1 : 0);
           

        // Register observer
        mContext.getContentResolver().registerContentObserver(
                Settings.Global.getUriFor(Settings.Global.WIFI_DISPLAY_DISPLAY_TOAST_TIME), false, mObserver);
        mContext.getContentResolver().registerContentObserver(
                Settings.Global.getUriFor(Settings.Global.WIFI_DISPLAY_DISPLAY_NOTIFICATION_TIME), false, mObserver);
        mContext.getContentResolver().registerContentObserver(
                Settings.Global.getUriFor(Settings.Global.WIFI_DISPLAY_SQC_INFO_ON), false, mObserver);

    }

    private final ContentObserver mObserver = new ContentObserver(new Handler()) {
            @Override
            public void onChange(boolean selfChange, Uri uri) {

                if (selfChange){
                    return;
                }                
                
                WFDCONTROLLER_DISPLAY_TOAST_TIME = Settings.Global.getInt(
                    mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_DISPLAY_TOAST_TIME, 20);

                WFDCONTROLLER_DISPLAY_NOTIFICATION_TIME = Settings.Global.getInt(
                    mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_DISPLAY_NOTIFICATION_TIME, 120);

                WFDCONTROLLER_SQC_INFO_ON = Settings.Global.getInt(
                    mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_SQC_INFO_ON, 0) != 0;
                WFDCONTROLLER_QE_ON = Settings.Global.getInt(
                    mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_QE_ON, 0) != 0;
                
       
                Slog.d(TAG, "onChange(), toast_time:" + WFDCONTROLLER_DISPLAY_TOAST_TIME +
                                         "noti_time:" + WFDCONTROLLER_DISPLAY_NOTIFICATION_TIME +
                                         "sqc:" + WFDCONTROLLER_SQC_INFO_ON +
                                         "qe:" + WFDCONTROLLER_QE_ON);
                  
 
            }
    };

    private void handleLevelChange(){
        
        if (mLevel < 0){ 
            
            // toast 
            if (!mToastTimerStarted){

                mHandler.postDelayed(
                    mDisplayToast, 
                    WFDCONTROLLER_DISPLAY_TOAST_TIME * 1000);
                mToastTimerStarted = true;
            }

            // notification 
            if (!mNotiTimerStarted){

                mHandler.postDelayed(
                    mDisplayNotification, 
                    WFDCONTROLLER_DISPLAY_NOTIFICATION_TIME * 1000);
                mNotiTimerStarted = true;
            }
            
        }
        else{

            clearNotify();
        }
            
    }

    private void clearNotify(){
        // toast 
        if (mToastTimerStarted){
            mHandler.removeCallbacks(mDisplayToast);
            mNotiTimerStarted = false;
        }
        
        // notification 
        if (mNotiTimerStarted){

            mHandler.removeCallbacks(mDisplayNotification);
            mNotiTimerStarted = false;
        }

        // Cancel the old notification if there is one.
        mNotificationManager.cancelAsUser(null,
            com.mediatek.internal.R.string.wifi_display_unstable_connection, UserHandle.ALL);       
    }

    private final Runnable mDisplayToast = new Runnable() {
        @Override
        public void run() {
            Slog.d(TAG, "mDisplayToast run()" + mLevel); 
            Resources mResource = Resources.getSystem();
            
            if (mLevel != 0){
                Toast.makeText(
                    mContext, 
                    mResource.getString(com.mediatek.internal.R.string.wifi_display_connection_is_not_steady), 
                    Toast.LENGTH_SHORT).show();   
            }

            mToastTimerStarted = false;
        }
    };
    
    private final Runnable mDisplayNotification = new Runnable() {
        @Override
        public void run() {
            Slog.d(TAG, "mDisplayNotification run()" + mLevel); 
            if (mLevel != 0){
                showNotification();
            }

            mNotiTimerStarted = false;
        }
    };

    private void showNotification(){

        Slog.d(TAG, "showNotification()"); 
        
        // Cancel the old notification if there is one.
        mNotificationManager.cancelAsUser(null,             //TAG
                com.mediatek.internal.R.string.wifi_display_unstable_connection,  //ID
                UserHandle.ALL);

        // Post the notification.
        Resources mResource = Resources.getSystem();

        Builder builder = new Notification.Builder(mContext)
                .setContentTitle(mResource.getString(com.mediatek.internal.R.string.wifi_display_unstable_connection))
                .setContentText(mResource.getString(com.mediatek.internal.R.string.wifi_display_unstable_suggestion))
                .setSmallIcon(R.drawable.ic_notify_wifidisplay)
                .setAutoCancel(true);
        
        Notification notification = new Notification.BigTextStyle(builder)
                .bigText(mResource.getString(com.mediatek.internal.R.string.wifi_display_unstable_suggestion))
                .build();
        mNotificationManager.notifyAsUser(null,                 //Tag
                    com.mediatek.internal.R.string.wifi_display_unstable_connection,  //ID
                    notification, UserHandle.ALL);
        
    }

    private void dialogReconnect() {
        showDialog(WFD_RECONNECT_DIALOG);

    }
    
    private final Runnable mReConnect = new Runnable() {
        @Override
        public void run() {
            if (null == mReConnectDevice) {
                Slog.w(TAG, "no reconnect device");
                return;
            }            

            if (DEBUG) {
                Slog.d(TAG, Thread.currentThread().getStackTrace()[2].getMethodName());
            }
            for (WifiP2pDevice device : mAvailableWifiDisplayPeers) {
                if (DEBUG) {
                    Slog.d(TAG, "\t" + describeWifiP2pDevice(device));
                }
                if (device.deviceAddress.equals(mReConnectDevice.deviceAddress)) {
                    connect(device);
                    return;
                }
            }
            
            mReConnection_Timeout_Remain_Seconds = mReConnection_Timeout_Remain_Seconds -
                (RECONNECT_RETRY_DELAY_MILLIS/1000);
            if (mReConnection_Timeout_Remain_Seconds > 0) {
                // check scan result per RECONNECT_RETRY_DELAY_MILLIS ms
                mHandler.postDelayed(mReConnect, RECONNECT_RETRY_DELAY_MILLIS);
            } else {
                Slog.e(TAG, "reconnect timeout!");
                Toast.makeText(mContext, com.mediatek.internal.R.string.wifi_display_disconnected
                    , Toast.LENGTH_SHORT).show();
                resetReconnectVariable();
                return;
            }
        }
    };

    private void resetReconnectVariable(){
        mReConnectDevice = null;
        mReConnection_Timeout_Remain_Seconds = 0;
        mReConnecting = false;
    }

    private void chooseNo_WifiDirectExcludeDialog () {
        /*M: ALPS00758891: notify apk wfd connection isn't connected*/
        actionAtDisconnected(null);

    }
    
    private void chooseNo_BTExcludeDialog () {
        Settings.Global.putInt(mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_ON, 0);

    }

    private void chooseNo_HDMIExcludeDialog_WfdUpdate () {
        Settings.Global.putInt(mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_ON, 0);
        updateWfdEnableState();

    }

    private void chooseNo_HDMIExcludeDialog_HDMIUpdate () {
        Settings.System.putInt(mContext.getContentResolver(), WFDCONTROLLER_HDMI_ENABLE_CONFIG, 0);
        if (null != mHdmiNative) {
            mHdmiNative.enableHDMI(false);
        }

    }

    private void prepareDialog(int dialogID) {
        Resources mResource = Resources.getSystem();

        if (WFD_WIFIP2P_EXCLUDED_DIALOG == dialogID) {
            // wifi direct excluded dialog
            mWifiDirectExcludeDialog = new AlertDialog.Builder(mContext)
                .setMessage(mResource.getString(com.mediatek.internal.R.string.wifi_display_wifi_p2p_disconnect_wfd_connect))
                .setPositiveButton(mResource.getString(R.string.dlg_ok), new OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            if (DEBUG) {
                                Slog.d(TAG, "disconnect previous Wi-Fi P2p connection");
                            }

                            mWifiP2pManager.removeGroup(mWifiP2pChannel, new ActionListener() {
                                @Override
                                public void onSuccess() {
                                    Slog.i(TAG, "Disconnected from previous Wi-Fi P2p device, succeess");
                                }

                                @Override
                                public void onFailure(int reason) {
                                    Slog.i(TAG, "Disconnected from previous Wi-Fi P2p device, failure = " + reason);
                                }
                            });
                            /*M: ALPS00758891: notify apk wfd connection isn't connected*/
                            actionAtDisconnected(null);
                            mUserDecided = true;
                        }
                    })
                .setNegativeButton(mResource.getString(R.string.decline), new OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            if (DEBUG) {
                                Slog.d(TAG, "keep previous Wi-Fi P2p connection");
                            }
                            chooseNo_WifiDirectExcludeDialog();
                            mUserDecided = true;
                        }
                    })
                .setOnCancelListener(new DialogInterface.OnCancelListener() {
                        @Override
                        public void onCancel(DialogInterface arg0) {
                            if (DEBUG) {
                                Slog.d(TAG, "onCancel(): keep previous Wi-Fi P2p connection");
                            }
                            chooseNo_WifiDirectExcludeDialog();
                            mUserDecided = true;
                        }
                    })
                .setOnDismissListener(new DialogInterface.OnDismissListener() {
                        @Override
                        public void onDismiss(DialogInterface arg0) {
                            if (DEBUG) {
                                Slog.d(TAG, "onDismiss()");
                            }
                            if (false == mUserDecided) {
                                chooseNo_WifiDirectExcludeDialog();
                            }
                        }
                    })
                .create();
            popupDialog(mWifiDirectExcludeDialog);

        } else if (WFD_BT_EXCLUDED_DIALOG == dialogID) {
            // BT excluded dialog
            mBTExcludeDialog = new AlertDialog.Builder(mContext)
                .setMessage(mResource.getString(com.mediatek.internal.R.string.wifi_display_bt_hdmi_off_wfd_on))
                .setPositiveButton(mResource.getString(R.string.dlg_ok), new OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            if (DEBUG) {
                                Slog.d(TAG, "user wants to use wifidisplay");
                            }
                            //wifidisplay
                            Settings.Global.putInt(mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_ON, 1);
                            mWifiDisplayOnSetting = true;
                            updateWfdEnableState();
                            //BT
                            Settings.Global.putInt(mContext.getContentResolver(), Settings.Global.BLUETOOTH_ON, 0);
                            if (null != mBTAdapter) {
                                mBTAdapter.disable();
                            }
                            //HDMI
                            Settings.System.putInt(mContext.getContentResolver(), WFDCONTROLLER_HDMI_ENABLE_CONFIG, 0);
                            if (null != mHdmiNative) {
                                mHdmiNative.enableHDMI(false);
                            }
                            mUserDecided = true;
                        }
                    })
                .setNegativeButton(mResource.getString(R.string.decline), new OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            if (DEBUG) {
                                Slog.d(TAG, "user wants to keep BT");
                            }
                            chooseNo_BTExcludeDialog();
                            mUserDecided = true;
                        }
                    })
                .setOnCancelListener(new DialogInterface.OnCancelListener() {
                        @Override
                        public void onCancel(DialogInterface arg0) {
                            if (DEBUG) {
                                Slog.d(TAG, "onCancel(): keep BT");
                            }
                            chooseNo_BTExcludeDialog();
                            mUserDecided = true;
                        }
                    })
                .setOnDismissListener(new DialogInterface.OnDismissListener() {
                        @Override
                        public void onDismiss(DialogInterface arg0) {
                            if (DEBUG) {
                                Slog.d(TAG, "onDismiss()");
                            }
                            if (false == mUserDecided) {
                                chooseNo_BTExcludeDialog();
                            }
                        }
                    })
                .create();
            popupDialog(mBTExcludeDialog);

        } else if (WFD_HDMI_EXCLUDED_DIALOG_WFD_UPDATE == dialogID) {
            // HDMI excluded dialog, WFD update
            mHDMIExcludeDialog_WfdUpdate = new AlertDialog.Builder(mContext)
                .setMessage(mResource.getString(com.mediatek.internal.R.string.wifi_display_bt_hdmi_off_wfd_on))
                .setPositiveButton(mResource.getString(R.string.dlg_ok), new OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            if (DEBUG) {
                                Slog.d(TAG, "WifiDisplay on, user turn off HDMI");
                            }
                            //HDMI
                            Settings.System.putInt(mContext.getContentResolver(), WFDCONTROLLER_HDMI_ENABLE_CONFIG, 0);
                            if (null != mHdmiNative) {
                                mHdmiNative.enableHDMI(false);
                            }
                            //BT
                            Settings.Global.putInt(mContext.getContentResolver(), Settings.Global.BLUETOOTH_ON, 0);
                            if (null != mBTAdapter) {
                                mBTAdapter.disable();
                            }
                            updateWfdEnableState();
                            mUserDecided = true;
                        }
                    })
                .setNegativeButton(mResource.getString(R.string.decline), new OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            if (DEBUG) {
                                Slog.d(TAG, "WifiDisplay on, user DON'T turn off HDMI -> turn off WifiDisplay");
                            }
                            chooseNo_HDMIExcludeDialog_WfdUpdate();
                            mUserDecided = true;
                        }
                    })
                .setOnCancelListener(new DialogInterface.OnCancelListener() {
                        @Override
                        public void onCancel(DialogInterface arg0) {
                            if (DEBUG) {
                                Slog.d(TAG, "onCancel(): WifiDisplay on, user DON'T turn off HDMI -> turn off WifiDisplay");
                            }
                            chooseNo_HDMIExcludeDialog_WfdUpdate();
                            mUserDecided = true;
                        }
                    })
                .setOnDismissListener(new DialogInterface.OnDismissListener() {
                        @Override
                        public void onDismiss(DialogInterface arg0) {
                            if (DEBUG) {
                                Slog.d(TAG, "onDismiss()");
                            }
                            if (false == mUserDecided) {
                                chooseNo_HDMIExcludeDialog_WfdUpdate();
                            }
                        }
                    })  
                .create();
            popupDialog(mHDMIExcludeDialog_WfdUpdate);

        } else if (WFD_HDMI_EXCLUDED_DIALOG_HDMI_UPDATE == dialogID) {
            // HDMI excluded dialog, HDMI update
            mHDMIExcludeDialog_HDMIUpdate = new AlertDialog.Builder(mContext)
                .setMessage(mResource.getString(com.mediatek.internal.R.string.wifi_display_wfd_off_hdmi_on))
                .setPositiveButton(mResource.getString(R.string.dlg_ok), new OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            if (DEBUG) {
                                Slog.d(TAG, "HDMI on, turn off WifiDisplay");
                            }
                            Settings.Global.putInt(mContext.getContentResolver(), Settings.Global.WIFI_DISPLAY_ON, 0);
                            mUserDecided = true;
                        }
                    })
                .setNegativeButton(mResource.getString(R.string.decline), new OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            if (DEBUG) {
                                Slog.d(TAG, "HDMI on, user DON'T turn off WifiDisplay -> turn off HDMI");
                            }
                            chooseNo_HDMIExcludeDialog_HDMIUpdate();
                            mUserDecided = true;
                        }
                    })
                .setOnCancelListener(new DialogInterface.OnCancelListener() {
                        @Override
                        public void onCancel(DialogInterface arg0) {
                            if (DEBUG) {
                                Slog.d(TAG, "onCancel(): HDMI on, user DON'T turn off WifiDisplay -> turn off HDMI");
                            }
                            chooseNo_HDMIExcludeDialog_HDMIUpdate();
                            mUserDecided = true;
                        }
                    })
                .setOnDismissListener(new DialogInterface.OnDismissListener() {
                        @Override
                        public void onDismiss(DialogInterface arg0) {
                            if (DEBUG) {
                                Slog.d(TAG, "onDismiss()");
                            }
                            if (false == mUserDecided) {
                                chooseNo_HDMIExcludeDialog_HDMIUpdate();
                            }
                        }
                    })
                .create();
            popupDialog(mHDMIExcludeDialog_HDMIUpdate);

        } else if (WFD_RECONNECT_DIALOG == dialogID) {
            // re-connect dialog
            mReConnecteDialog = new AlertDialog.Builder(mContext)
                .setTitle(com.mediatek.internal.R.string.wifi_display_reconnect)
                .setMessage(com.mediatek.internal.R.string.wifi_display_disconnect_then_reconnect)
                .setPositiveButton(mResource.getString(R.string.dlg_ok), new OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            if (DEBUG) {
                                Slog.d(TAG, "user want to reconnect");
                            }
                            //scan first
                            requestScan();
                            // check scan result per RECONNECT_RETRY_DELAY_MILLIS ms
                            mReConnection_Timeout_Remain_Seconds = CONNECTION_TIMEOUT_SECONDS;
                            mHandler.postDelayed(mReConnect, RECONNECT_RETRY_DELAY_MILLIS);
                        }
                    })
                .setNegativeButton(mResource.getString(R.string.decline), new OnClickListener() {
                        @Override
                        public void onClick(DialogInterface dialog, int which) {
                            if (DEBUG) {
                                Slog.d(TAG, "user want nothing");
                            }
                        }
                    })
                .setOnCancelListener(new DialogInterface.OnCancelListener() {
                        @Override
                        public void onCancel(DialogInterface arg0) {
                            if (DEBUG) {
                                Slog.d(TAG, "user want nothing");
                            }
                        }
                    })
                .create();
            popupDialog(mReConnecteDialog);

        }

    }

    private void popupDialog(AlertDialog dialog) {
        dialog.getWindow().setType(WindowManager.LayoutParams.TYPE_SYSTEM_ALERT);
        dialog.getWindow().getAttributes().privateFlags |=
                WindowManager.LayoutParams.PRIVATE_FLAG_SHOW_FOR_ALL_USERS;
        dialog.show();

    }

    private void showDialog(int dialogID) {
        mUserDecided = false;
        prepareDialog(dialogID);

    }

    private void dismissDialog() {
        dismissDialogDetail(mWifiDirectExcludeDialog);
        dismissDialogDetail(mBTExcludeDialog);
        dismissDialogDetail(mHDMIExcludeDialog_WfdUpdate);
        dismissDialogDetail(mHDMIExcludeDialog_HDMIUpdate);
        dismissDialogDetail(mReConnecteDialog);

    }

    private void dismissDialogDetail(AlertDialog dialog) {
        if (null!=dialog && dialog.isShowing()) {
            dialog.dismiss();
        }

    }

    /* [google mechanism] how to get connection state? from WifiDisplaySettings.java
        -SettingProvider: WIFI_DISPLAY_ON
        -Broadcast ACTION_WIFI_DISPLAY_STATUS_CHANGED
        -WifiDisplayStatus.getActiveDisplayState(): connect state
        -WifiDisplayStatus.getFeatureState(): feature state
    */    
    ///@}
}
