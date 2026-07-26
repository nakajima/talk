//! Artifact manifests (ADR 0043): the provenance record shipped beside a
//! checked-in bytecode artifact. A manifest ties the artifact to the
//! sources it was built from and the wire-format version needed to load
//! it; verification fails closed on any mismatch, so editing a source
//! without regenerating the artifact cannot pass validation.

use sha2::{Digest, Sha256};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactManifest {
    /// The bytecode wire-format version the artifact was encoded with.
    pub format_version: u32,
    /// Digest of the canonical source set the artifact was built from.
    pub source_digest: String,
    /// Digest of the artifact bytes themselves.
    pub artifact_digest: String,
}

/// Digest a source set independent of supply order: entries sort by name
/// and hash as length-prefixed name/content pairs, so neither
/// concatenation ambiguity nor discovery order can alias two sets.
pub fn source_digest(sources: &[(String, String)]) -> String {
    let mut entries: Vec<&(String, String)> = sources.iter().collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    let mut hasher = Sha256::new();
    for (name, content) in entries {
        hasher.update(u64::try_from(name.len()).unwrap_or_default().to_le_bytes());
        hasher.update(name.as_bytes());
        hasher.update(
            u64::try_from(content.len())
                .unwrap_or_default()
                .to_le_bytes(),
        );
        hasher.update(content.as_bytes());
    }
    format!("{:x}", hasher.finalize())
}

pub fn artifact_digest(image: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(image);
    format!("{:x}", hasher.finalize())
}

impl ArtifactManifest {
    pub fn compute(sources: &[(String, String)], image: &[u8]) -> Self {
        Self {
            format_version: talk_runtime::bytecode::FORMAT_VERSION,
            source_digest: source_digest(sources),
            artifact_digest: artifact_digest(image),
        }
    }

    /// Fail-closed validation: the artifact bytes and the sources must
    /// both match, and the recorded format version must be the one this
    /// compiler loads.
    pub fn verify(&self, sources: &[(String, String)], image: &[u8]) -> Result<(), String> {
        if self.format_version != talk_runtime::bytecode::FORMAT_VERSION {
            return Err(format!(
                "artifact manifest records bytecode format {} but this compiler loads {}; regenerate the artifact",
                self.format_version,
                talk_runtime::bytecode::FORMAT_VERSION
            ));
        }
        let actual = artifact_digest(image);
        if self.artifact_digest != actual {
            return Err("artifact bytes do not match their manifest; regenerate the artifact".into());
        }
        let actual = source_digest(sources);
        if self.source_digest != actual {
            return Err(
                "sources have changed since the artifact was generated; regenerate the artifact"
                    .into(),
            );
        }
        Ok(())
    }

    pub fn to_text(&self) -> String {
        format!(
            "format_version: {}\nsource_digest: {}\nartifact_digest: {}\n",
            self.format_version, self.source_digest, self.artifact_digest
        )
    }

    pub fn parse(text: &str) -> Result<Self, String> {
        let mut format_version = None;
        let mut source_digest = None;
        let mut artifact_digest = None;
        for line in text.lines() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            let Some((key, value)) = line.split_once(':') else {
                return Err(format!("malformed manifest line: `{line}`"));
            };
            let value = value.trim();
            match key.trim() {
                "format_version" => {
                    format_version = Some(
                        value
                            .parse::<u32>()
                            .map_err(|_| format!("malformed format_version: `{value}`"))?,
                    )
                }
                "source_digest" => source_digest = Some(value.to_string()),
                "artifact_digest" => artifact_digest = Some(value.to_string()),
                unknown => return Err(format!("unknown manifest key: `{unknown}`")),
            }
        }
        Ok(Self {
            format_version: format_version.ok_or("manifest missing format_version")?,
            source_digest: source_digest.ok_or("manifest missing source_digest")?,
            artifact_digest: artifact_digest.ok_or("manifest missing artifact_digest")?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sources() -> Vec<(String, String)> {
        vec![
            ("Lexer.tlk".into(), "func lex() -> Int { 1 }".into()),
            ("Parser.tlk".into(), "func parse() -> Int { 2 }".into()),
        ]
    }

    #[test]
    fn manifest_round_trips_through_text() {
        let manifest = ArtifactManifest::compute(&sources(), b"image-bytes");
        let parsed = ArtifactManifest::parse(&manifest.to_text()).expect("parse");
        assert_eq!(parsed, manifest);
    }

    #[test]
    fn source_digest_is_order_independent_but_name_sensitive() {
        let forward = source_digest(&sources());
        let mut reversed = sources();
        reversed.reverse();
        assert_eq!(forward, source_digest(&reversed));

        let mut renamed = sources();
        renamed[0].0 = "Lexer2.tlk".into();
        assert_ne!(forward, source_digest(&renamed));
    }

    #[test]
    fn verification_fails_closed_on_any_mismatch() {
        let manifest = ArtifactManifest::compute(&sources(), b"image-bytes");
        manifest.verify(&sources(), b"image-bytes").expect("clean");

        let tampered = manifest.verify(&sources(), b"other-bytes");
        assert!(tampered.err().expect("tampered image").contains("artifact"));

        let mut edited = sources();
        edited[0].1.push_str("\n// edited");
        let stale = manifest.verify(&edited, b"image-bytes");
        assert!(stale.err().expect("edited source").contains("sources"));

        let mut wrong_version = manifest.clone();
        wrong_version.format_version += 1;
        let version = wrong_version.verify(&sources(), b"image-bytes");
        assert!(version.err().expect("format skew").contains("format"));
    }
}
