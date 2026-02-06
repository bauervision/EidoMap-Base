// Assets/EidoMap/Runtime/Maps/MapView.AoiTrainingUi.cs
using System;
using TMPro;
using UnityEngine;
using UnityEngine.UI;

namespace EidoMap
{
    public partial class MapView
    {
        public enum AoiTrainingState
        {
            Valid = 0,
            Warn = 1,
            Invalid = 2,
            Hunting = 3,
        }

        [Header("Training UI (Foot / VR)")]
        [Tooltip("Optional TMP label to show max walk time and capture validity.")]
        [SerializeField] private TMP_Text trainingHudText;

        [Tooltip("Optional: set if you want this code to enable/disable the Capture button automatically.")]
        [SerializeField] private Button captureButton;

        [Tooltip("If true, Capture button is disabled when AOI is invalid/hunting.")]
        [SerializeField] private bool disableCaptureWhenUnavailable = true;

        [Header("Walk Time Model")]
        [Tooltip("Assumed walk speed in meters/second. 1.3 m/s is a typical adult walking speed.")]
        [SerializeField] private float walkSpeedMetersPerSec = 1.3f;

        [Header("Training Constraints (meters)")]
        [Tooltip("Below this, AOI is considered very small; we warn but still allow capture.")]
        [SerializeField] private float minAoiShortSideMeters = 250f;

        [Tooltip("At/above this, show warning but still allow capture.")]
        [SerializeField] private float warnAoiShortSideMeters = 1500f;

        [Tooltip("Above this, AOI is too large for foot-based training (capture disabled).")]
        [SerializeField] private float maxAoiShortSideMeters = 2000f;

        [Tooltip("Above this, we consider the user to be 'Location Hunting' (hide masks; capture disabled).")]
        [SerializeField] private float huntingAoiShortSideMeters = 3500f;

        [Header("Mask Visuals (each is a GameObject with children visuals)")]
        [SerializeField] private GameObject maskValid;
        [SerializeField] private GameObject maskWarn;
        [SerializeField] private GameObject maskInvalid;

        [Header("Hunting UI Copy")]
        [SerializeField] private string huntingMessage = "Location Hunting...";
        [SerializeField] private string invalidMessage = "AOI too large for foot training. Zoom in to reduce area.";
        [SerializeField] private string warnMessage = "Large AOI. Long walking distances.";
        [SerializeField] private string validMessage = "AOI size suitable for foot training.";
        [SerializeField] private string tinyWarnMessage = "AOI is very small for foot training.";

        private AoiTrainingState _lastTrainingState = (AoiTrainingState)(-1);

        private struct TrainingEval
        {
            public AoiTrainingState state;
            public float shortSideMeters;
            public float maxWalkSeconds; // from center to nearest edge: shortSide/2 / speed
            public bool canCapture;
            public string message;
        }

        /// <summary>
        /// Call this whenever AOI bounds change (including zoom changes).
        /// </summary>
        private void UpdateTrainingUiForAoi(AoiBounds b)
        {
            var eval = EvaluateTrainingAoi(b);

            ApplyTrainingMask(eval.state);
            ApplyCaptureEnabled(eval.canCapture);

            if (trainingHudText)
                trainingHudText.text = BuildTrainingHudText(eval);

            if (eval.state != _lastTrainingState)
            {
                _lastTrainingState = eval.state;
                OnTrainingStateChanged(eval.state, eval);
            }
        }

        private void OnTrainingStateChanged(AoiTrainingState state, TrainingEval eval)
        {
            // no-op by default (hook if you want sounds/toasts)
        }

        private TrainingEval EvaluateTrainingAoi(AoiBounds b)
        {
            // Uses helper in TerrainRgbTiles.cs
            ComputeAoiMeters(b, out float wMeters, out float hMeters);
            float shortSide = Mathf.Min(wMeters, hMeters);

            float speed = Mathf.Max(0.1f, walkSpeedMetersPerSec);
            float maxWalkSeconds = (shortSide * 0.5f) / speed;

            // Hunting: hide masks, disable capture, show hunting message.
            if (shortSide >= Mathf.Max(maxAoiShortSideMeters, huntingAoiShortSideMeters))
            {
                return new TrainingEval
                {
                    state = AoiTrainingState.Hunting,
                    shortSideMeters = shortSide,
                    maxWalkSeconds = maxWalkSeconds,
                    canCapture = false,
                    message = huntingMessage
                };
            }

            // Invalid (still show red mask): disable capture.
            if (shortSide > Mathf.Max(0f, maxAoiShortSideMeters))
            {
                return new TrainingEval
                {
                    state = AoiTrainingState.Invalid,
                    shortSideMeters = shortSide,
                    maxWalkSeconds = maxWalkSeconds,
                    canCapture = false,
                    message = invalidMessage
                };
            }

            // Tiny warn (optional): allow capture but warn.
            if (shortSide < Mathf.Max(0f, minAoiShortSideMeters))
            {
                return new TrainingEval
                {
                    state = AoiTrainingState.Warn,
                    shortSideMeters = shortSide,
                    maxWalkSeconds = maxWalkSeconds,
                    canCapture = true,
                    message = tinyWarnMessage
                };
            }

            // Warning range: allow capture, show warn mask.
            if (shortSide >= Mathf.Max(0f, warnAoiShortSideMeters))
            {
                return new TrainingEval
                {
                    state = AoiTrainingState.Warn,
                    shortSideMeters = shortSide,
                    maxWalkSeconds = maxWalkSeconds,
                    canCapture = true,
                    message = warnMessage
                };
            }

            // Valid
            return new TrainingEval
            {
                state = AoiTrainingState.Valid,
                shortSideMeters = shortSide,
                maxWalkSeconds = maxWalkSeconds,
                canCapture = true,
                message = validMessage
            };
        }

        private void ApplyTrainingMask(AoiTrainingState state)
        {
            // Hunting: hide all masks.
            if (state == AoiTrainingState.Hunting)
            {
                if (maskValid) maskValid.SetActive(false);
                if (maskWarn) maskWarn.SetActive(false);
                if (maskInvalid) maskInvalid.SetActive(false);
                return;
            }

            if (maskValid) maskValid.SetActive(state == AoiTrainingState.Valid);
            if (maskWarn) maskWarn.SetActive(state == AoiTrainingState.Warn);
            if (maskInvalid) maskInvalid.SetActive(state == AoiTrainingState.Invalid);
        }

        private void ApplyCaptureEnabled(bool canCapture)
        {
            if (!captureButton) return;
            if (!disableCaptureWhenUnavailable) return;

            captureButton.interactable = canCapture;
        }

        private string BuildTrainingHudText(TrainingEval eval)
        {
            // In hunting mode, we intentionally show copy only (no walk time).
            if (eval.state == AoiTrainingState.Hunting)
                return eval.message;

            string time = FormatMinutesSeconds(eval.maxWalkSeconds);
            string line1 = $"Max walk to edge (from center): {time}";
            string line2 = $"AOI short-side: {eval.shortSideMeters:0} m";
            string line3 = eval.message;

            return $"{line1}\n{line2}\n{line3}";
        }

        private static string FormatMinutesSeconds(float seconds)
        {
            if (!float.IsFinite(seconds) || seconds <= 0f) return "0:00";

            int s = Mathf.RoundToInt(seconds);
            int m = s / 60;
            int ss = s % 60;
            return $"{m}:{ss:00}";
        }
    }
}
